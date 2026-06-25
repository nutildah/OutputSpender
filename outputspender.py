import tkinter as tk
from tkinter import messagebox, Toplevel, Listbox, Scrollbar, END, Button, Label, ttk
import hashlib
import base58
import struct
import webbrowser
import sys
import os
import time
import requests
import threading
import concurrent.futures
from requests.exceptions import HTTPError
from ecdsa import SigningKey, SECP256k1
from ecdsa.util import sigencode_der
from ecdsa import util
from tkinter import font as tkfont


# ============================
# Helper: PyInstaller resource path
# ============================
def resource_path(relative_path):
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)


# ============================
# Scanning helpers
# ============================
API_BASE = "https://mempool.space/api"
CUTOFF_TIMESTAMP = 1417478400  # Dec 2, 2014


def get_all_txids(address: str):
    tx_list = []
    last_seen = None
    page = 0

    while True:
        url = f"{API_BASE}/address/{address}/txs"
        if last_seen:
            url += f"?after_txid={last_seen}"

        for attempt in range(5):
            try:
                r = requests.get(url, timeout=20)
                if r.status_code == 429:
                    time.sleep(2 ** attempt)
                    continue
                r.raise_for_status()
                break
            except HTTPError:
                if r.status_code == 429:
                    continue
                raise

        txs = r.json()
        if not txs:
            break

        for tx in txs:
            block_time = tx.get("status", {}).get("block_time", 0)
            tx_list.append({"txid": tx["txid"], "block_time": block_time})

        last_seen = txs[-1]["txid"]
        page += 1
        time.sleep(1.5)

    return tx_list


def get_full_tx(txid: str):
    url = f"{API_BASE}/tx/{txid}"
    for attempt in range(5):
        try:
            r = requests.get(url, timeout=15)
            if r.status_code == 429:
                time.sleep(2 ** attempt)
                continue
            r.raise_for_status()
            return r.json()
        except HTTPError:
            if r.status_code == 429:
                continue
            raise
    raise Exception(f"Failed to fetch {txid}")


def is_fake_multisig(spk_hex: str) -> bool:
    if not spk_hex:
        return False
    s = spk_hex.lower()
    return s.startswith("51") and "21" in s and s.endswith("ae")


def address_in_inputs(tx, target_address: str) -> bool:
    for vin in tx.get("vin", []):
        prev_addr = vin.get("prevout", {}).get("scriptpubkey_address")
        if prev_addr == target_address:
            return True
    return False


def is_unspent(txid: str, vout: int) -> bool:
    try:
        r = requests.get(f"{API_BASE}/tx/{txid}/outspend/{vout}", timeout=10)
        r.raise_for_status()
        return r.json().get("spent") is False
    except:
        return False

def scan_address_for_bare_multisig_grouped(address: str, progress_cb=None):
    tx_list = get_all_txids(address)          # This part is already reasonably fast
    if not tx_list:
        return {}

    # Filter to only recent transactions
    recent_txs = [tx for tx in tx_list if tx["block_time"] >= CUTOFF_TIMESTAMP]
    
    grouped = {}
    total = len(recent_txs)

    print(f"Checking {total} recent transactions...")  # for console debugging

    # Use ThreadPool to fetch multiple txs in parallel (max 4 at a time)
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
        future_to_txid = {
            executor.submit(get_full_tx, tx_info["txid"]): tx_info["txid"]
            for tx_info in recent_txs
        }

        for i, future in enumerate(concurrent.futures.as_completed(future_to_txid), 1):
            txid = future_to_txid[future]
            
            if progress_cb:
                progress_cb(i, total, txid)

            try:
                tx = future.result()
            except Exception:
                continue

            if not address_in_inputs(tx, address):
                continue

            for vout_idx, vout in enumerate(tx.get("vout", [])):
                spk_hex = vout.get("scriptpubkey", "")

                if not is_fake_multisig(spk_hex):
                    continue
                if not is_unspent(txid, vout_idx):
                    continue

                value = vout.get("value", 0)

                if txid not in grouped:
                    grouped[txid] = {"total_sats": 0, "outputs": []}

                grouped[txid]["total_sats"] += value
                grouped[txid]["outputs"].append({
                    "vout": vout_idx,
                    "value_sats": value,
                    "scriptpubkey": spk_hex
                })

    return grouped

# ============================
# Address → scriptPubKey helpers
# ============================

BECH32_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"

def bech32_polymod(values):
    GEN = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
    chk = 1
    for v in values:
        b = (chk >> 25)
        chk = ((chk & 0x1ffffff) << 5) ^ v
        for i in range(5):
            chk ^= GEN[i] if ((b >> i) & 1) else 0
    return chk

def bech32_hrp_expand(hrp):
    return [ord(x) >> 5 for x in hrp] + [0] + [ord(x) & 31 for x in hrp]

def bech32_verify_checksum(hrp, data):
    return bech32_polymod(bech32_hrp_expand(hrp) + data) == 1

def bech32_decode(addr):
    addr = addr.lower()
    if addr[:3] != "bc1":
        return None, None
    pos = addr.rfind('1')
    if pos < 1 or pos + 7 > len(addr):
        return None, None
    hrp = addr[:pos]
    data = []
    for c in addr[pos + 1:]:
        if c not in BECH32_CHARSET:
            return None, None
        data.append(BECH32_CHARSET.find(c))
    if not bech32_verify_checksum(hrp, data):
        return None, None
    return hrp, data[:-6]

def convertbits(data, frombits, tobits, pad=True):
    acc = 0
    bits = 0
    ret = []
    maxv = (1 << tobits) - 1
    for value in data:
        if value < 0 or (value >> frombits):
            return None
        acc = (acc << frombits) | value
        bits += frombits
        while bits >= tobits:
            bits -= tobits
            ret.append((acc >> bits) & maxv)
    if pad:
        if bits:
            ret.append((acc << (tobits - bits)) & maxv)
    elif bits >= frombits or ((acc << (tobits - bits)) & maxv):
        return None
    return ret


def address_to_scriptpubkey(addr):
    if addr.startswith("1"):
        decoded = base58.b58decode_check(addr)
        h160 = decoded[1:]
        return "76a914" + h160.hex() + "88ac"

    if addr.startswith("3"):
        decoded = base58.b58decode_check(addr)
        h160 = decoded[1:]
        return "a914" + h160.hex() + "87"

    if addr.lower().startswith("bc1q"):
        hrp, data = bech32_decode(addr)
        if hrp != "bc":
            raise ValueError("Only mainnet bc1 addresses supported")
        witver = data[0]
        prog = convertbits(data[1:], 5, 8, False)
        prog = bytes(prog)
        if witver != 0 or len(prog) != 20:
            raise ValueError("Only P2WPKH (v0, 20-byte) supported")
        return "0014" + prog.hex()

    raise ValueError("Unsupported address type (only 1, 3, bc1q supported)")


# ============================
# Transaction helper functions
# ============================

def sha256(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()

def dsha256(b: bytes) -> bytes:
    return sha256(sha256(b))

def encode_varint(i: int) -> bytes:
    if i < 0xfd:
        return bytes([i])
    elif i <= 0xFFFF:
        return b"\xfd" + struct.pack("<H", i)
    elif i <= 0xFFFFFFFF:
        return b"\xfe" + struct.pack("<I", i)
    else:
        return b"\xff" + struct.pack("<Q", i)

def normalize_low_s(sig_bytes: bytes) -> bytes:
    r, s = util.sigdecode_der(sig_bytes, SECP256k1.order)
    if s > SECP256k1.order // 2:
        s = SECP256k1.order - s
    return util.sigencode_der(r, s, SECP256k1.order)


# ============================
# GUI Application
# ============================

class TxBuilderGUI:
    def __init__(self, root):
        self.root = root
        root.title("OutputSpender: Counterparty Bare-Multisig Transaction Builder")

        default_font = tkfont.nametofont("TkDefaultFont")
        default_font.configure(size=int(default_font.cget("size") * 1.25))
        root.option_add("*Font", default_font)

        root.geometry("945x680")
        root.minsize(800, 550)
        root.resizable(True, True)

        self.container = tk.Frame(root)
        self.container.pack(fill="both", expand=True)

        self.canvas = tk.Canvas(self.container)
        self.scrollbar = tk.Scrollbar(self.container, orient="vertical", command=self.canvas.yview)

        self.outer = tk.Frame(self.canvas, padx=20, pady=20)
        self.scrollable_frame = tk.Frame(self.outer)

        self.scrollable_frame.pack(fill="both", expand=True)
        self.outer.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))

        self.canvas.create_window((0, 0), window=self.outer, anchor="nw")
        self.canvas.configure(yscrollcommand=self.scrollbar.set)

        self.canvas.pack(side="left", fill="both", expand=True)
        self.scrollbar.pack(side="right", fill="y")

        self.canvas.bind_all("<MouseWheel>", lambda e: self.canvas.yview_scroll(int(-1 * (e.delta / 120)), "units"))

        # Title + Subtitle
        title_font = tkfont.Font(family="Segoe UI", size=18, weight="bold")
        body_font = tkfont.Font(family="Segoe UI", size=12)

        title_label = tk.Label(self.scrollable_frame, text="Spend Fake Multisig Outputs from Counterparty Transactions",
                               font=title_font, anchor="w", justify="left")
        title_label.pack(anchor="w", pady=(0, 5))

        subtitle_label = tk.Label(self.scrollable_frame, 
                                  text="Build & broadcast a Bitcoin transaction to recover any 'hidden' outputs from Dec 2014 - present.",
                                  font=body_font, anchor="w", justify="left", wraplength=700)
        subtitle_label.pack(anchor="w", pady=(0, 20))

        # Scan Address
        scan_frame = tk.Frame(self.scrollable_frame)
        scan_frame.pack(fill="x", pady=(0, 12), anchor="w")

        tk.Label(scan_frame, text="Scan Address for unspent fake multisig outputs:").pack(side="left", padx=(0, 5))
        self.scan_address_entry = tk.Entry(scan_frame, width=55)
        self.scan_address_entry.pack(side="left", padx=(0, 8))

        tk.Button(scan_frame, text="Scan", command=self.start_scan, width=12).pack(side="left", padx=(5, 0))

        # Progress bar
        self.progress_frame = tk.Frame(self.scrollable_frame)
        self.progress_frame.pack(fill="x", pady=(5, 15))

        self.scan_progress_label = tk.Label(self.progress_frame, text="", anchor="w")
        self.scan_progress_label.pack(side="left", padx=(0, 10))

        self.progress_bar = ttk.Progressbar(self.progress_frame, length=500, mode='determinate')
        self.progress_bar.pack(side="left", fill="x", expand=True)

        # Global fields
        tk.Label(self.scrollable_frame, text="Transaction ID (all inputs come from this TX):").pack(anchor="w", pady=(10, 2))
        self.txid_entry = tk.Entry(self.scrollable_frame, width=80)
        self.txid_entry.pack(fill="x", pady=(0, 8))

        tk.Label(self.scrollable_frame, text="Private Key (WIF):").pack(anchor="w", pady=(8, 2))
        self.wif_entry = tk.Entry(self.scrollable_frame, width=80, show="*")
        self.wif_entry.pack(fill="x", pady=(0, 8))

        tk.Label(self.scrollable_frame, text="\nDestination Address:").pack(anchor="w", pady=(8, 2))
        self.dest_entry = tk.Entry(self.scrollable_frame, width=80)
        self.dest_entry.pack(fill="x", pady=(0, 8))

        # Inputs section
        tk.Label(self.scrollable_frame, text="\nNumber of Inputs:").pack(anchor="w", pady=(12, 2))
        self.num_inputs_entry = tk.Entry(self.scrollable_frame, width=10)
        self.num_inputs_entry.pack(anchor="w", pady=(0, 8))

        tk.Button(self.scrollable_frame, text="Create Input Fields", command=self.create_input_fields).pack(anchor="w", pady=(5, 15))

        self.inputs_frame = tk.Frame(self.scrollable_frame)
        self.inputs_frame.pack(fill="x", pady=(0, 15))

        # Fee section
        fee_frame = tk.Frame(self.scrollable_frame)
        fee_frame.pack(fill="x", pady=(0, 15))
        tk.Label(fee_frame, text="Fee (sats):").pack(anchor="w")
        self.fee_entry = tk.Entry(fee_frame, width=20)
        self.fee_entry.pack(anchor="w")

        # Build button
        tk.Button(self.scrollable_frame, text="Build Transaction", command=self.build_transaction).pack(pady=(5, 15))

        # Output hex box
        tk.Label(self.scrollable_frame, text="\nSigned Transaction Hex:").pack(anchor="w", pady=(10, 2))
        self.hex_box = tk.Text(self.scrollable_frame, height=12, width=100)
        self.hex_box.pack(fill="both", expand=True, pady=(0, 8))

        tk.Button(self.scrollable_frame, text="Copy to Clipboard", command=self.copy_hex).pack(pady=(5, 0))

        link = tk.Label(self.scrollable_frame, text="Broadcast Transaction", fg="blue", cursor="hand2")
        link.pack(pady=(15, 5))
        link.bind("<Button-1>", lambda e: webbrowser.open("https://blockstream.info/tx/push"))

        # Donation
        donate_link = tk.Label(self.scrollable_frame,
                               text="donations: bc1qza7kyd89567rr2n8alazy00h9hj065fved7gvy (tokenscan link)",
                               fg="blue", cursor="hand2")
        donate_link.pack(pady=(20, 5))
        donate_link.bind("<Button-1>", lambda e: webbrowser.open(
            "https://tokenscan.io/address/bc1qza7kyd89567rr2n8alazy00h9hj065fved7gvy"))

        email_label = tk.Label(self.scrollable_frame,
                               text="email nutildah@dogermint.com for questions & comments",
                               fg="#808080", font=("Segoe UI", 9))
        email_label.pack(pady=(2, 0))

        # Instructions button
        self.instructions_button = tk.Button(self.scrollable_frame, text="Show Instructions",
                                             command=self.toggle_instructions)
        self.instructions_button.pack(anchor="w", pady=(25, 5))

        self.instructions_frame = tk.Frame(self.scrollable_frame)
        self.instructions_frame.pack_forget()

        instructions_text = (
    "Step 1. Enter an address to scan for transactions with fake multisig outputs "
    "(specific to Counterparty transactions). The scan will check your address history "
    "and return a list of transaction IDs with unspent multisig outputs. Be patient as "
    "this process can take several minutes for addresses with large transaction histories.\n\n"

    "Step 2. Click on the transaction ID for one of these transactions. This will open "
    "the corresponding tx page on mempool.space. Scroll down the page and click the "
    "\"Details\" button to the right of \"Inputs & Outputs\". This will expand the "
    "information to include the fields you need to create your spend transaction:\n\n"

    " - Transaction ID (txid): the string after \"/tx/\" in the browser address bar\n"
    " - Amount: sats in output, to the right of \"MULTISIG\" in the output area\n"
    " - ScriptPubKey (HEX): a long string of characters immediately below "
    "\"ScriptPubKey (ASM)\" in the output area\n"
    " - VOUT: the position of the output in its transaction (1st position: VOUT = 0, "
    "2nd position: VOUT = 1, 3rd position: VOUT = 2, etc.)\n\n"

    "Step 3. Locate the VOUT and ScriptPubKey for each output you want to spend.\n\n"

    "You will also need:\n"
    " - Private key of the scanned address\n"
    " - Bitcoin address to which you want to send BTC\n\n"

    "Step 4. Enter the transaction ID, private key, and number of inputs (total number "
    "of outputs to be spent from the same transaction ID). After double-checking "
    "everything is correct, press \"Create Input Fields\".\n\n"

    "Step 5. Enter the necessary data for each input:\n"
    " - VOUT: 1st output VOUT = 0; 2nd output VOUT = 1; 3rd output VOUT = 2; etc.\n"
    " - Amount (sats): amount of the output\n"
    " - Spend Amount (sats): amount you want to spend (difference goes to miners; "
    "100 sat minimum is recommended per input added to the transaction)\n"
    " - Bare Multisig scriptPubKey (hex): long string of digits below "
    "\"ScriptPubKey (ASM)\"\n\n"

    "A recommended transaction fee of slightly >1 sat/byte will be applied, but can be "
    "customized by the user (minimum of 100 sat per input strongly recommended). After "
    "double-checking to make sure everything is correct, press \"Build Transaction\".\n\n"

    "Step 6. If everything went according to plan, you should see a popup that says "
    "\"Transaction built. Fee = (Total Amount - Total Spend Amount). Output amount = "
    "(Total Spend Amount).\" Press the \"Copy to Clipboard\" button under Signed "
    "Transaction Hex.\n\n"

    "Step 7. You are now ready to broadcast the transaction to the Bitcoin network. "
    "Press the \"Broadcast Transaction\" link below the \"Copy to Clipboard\" button. "
    "This will bring you to Blockstream's transaction broadcast service. Paste your "
    "transaction hex into the box and press \"Broadcast transaction\". You will then be "
    "brought to the block explorer entry for your new transaction which will await "
    "confirmation in the mempool.\n\n"

    "If you get a message that says \"Transaction not found\", simply refresh the page. "
    "This means your broadcast was successful but the transaction page had not been "
    "created yet. If it says any other error message, double-check your fields as "
    "something is wrong in the construction of your transaction."
)

        instructions_label = tk.Label(self.instructions_frame, text=instructions_text,
                                      justify="left", anchor="w", wraplength=700)
        instructions_label.pack(anchor="w", pady=(5, 0))

        self.set_dark_mode()

    # ============================
    # Scan Address Feature
    # ============================
    def start_scan(self):
        addr = self.scan_address_entry.get().strip()
        if not addr:
            messagebox.showerror("Error", "Please enter a Bitcoin address.")
            return

        self.progress_bar['value'] = 0
        self.scan_progress_label.config(text="Starting scan (this may take a while)...")
        self.root.update_idletasks()

        def run_scan():
            def progress_cb(i, total, txid):
                progress = int((i / total) * 100)
                self.root.after(0, lambda: self.progress_bar.config(value=progress))
                self.root.after(0, lambda: self.scan_progress_label.config(
                    text=f"Scanning tx {i}/{total}: {txid[:16]}..."))

            try:
                grouped = scan_address_for_bare_multisig_grouped(addr, progress_cb=progress_cb)
                self.root.after(0, lambda: self.show_scan_results(grouped, addr))
            except Exception as e:
                self.root.after(0, lambda: messagebox.showerror("Scan Error", str(e)))
            finally:
                self.root.after(0, lambda: self.scan_progress_label.config(text="Scan complete."))

        threading.Thread(target=run_scan, daemon=True).start()

    def show_scan_results(self, grouped, address):
        if not grouped:
            messagebox.showinfo("Scan Complete", "No spendable outputs found.")
            return

        # Calculate grand total across all transactions
        grand_total_sats = sum(info["total_sats"] for info in grouped.values())

        win = Toplevel(self.root)
        win.title(f"Scan Results — {address}")
        win.geometry("900x520")

        Label(win, text=f"Found {len(grouped)} transaction(s) with unspent fake multisig outputs",
              font=("Segoe UI", 12, "bold")).pack(pady=(10, 2))

        # === NEW LINE: Total spendable sats ===
        Label(win, text=f"Total spendable sats: {grand_total_sats:,} sats",
              font=("Segoe UI", 11, "bold"), fg="#00cc00").pack(pady=(0, 10))

        Label(win, text="Double-click any row to open the transaction on mempool.space",
              font=("Segoe UI", 10), fg="#888888").pack(pady=(0, 10))

        listbox = Listbox(win, width=170, height=27, font=("Consolas", 10))
        scrollbar = Scrollbar(win, orient="vertical", command=listbox.yview)
        listbox.config(yscrollcommand=scrollbar.set)

        listbox.pack(side="left", fill="both", expand=True, padx=(20, 0))
        scrollbar.pack(side="right", fill="y")

        self._scan_results_flat = []
        for txid, info in grouped.items():
            total = info["total_sats"]
            line = f"{txid}   |   TOTAL {total:,} sats   |   {len(info['outputs'])} output(s)"
            listbox.insert(END, line)
            self._scan_results_flat.append((txid, info))

        def open_tx(event):
            sel = listbox.curselection()
            if not sel:
                return
            idx = sel[0]
            txid, _ = self._scan_results_flat[idx]
            webbrowser.open(f"https://mempool.space/tx/{txid}")

        listbox.bind("<Double-Button-1>", open_tx)

        Button(win, text="Use Selected Transaction", command=self.use_selected_result,
               bg="#3a3a3a", fg="white").pack(pady=15)

    def use_selected_result(self):
        # Placeholder - you can expand later if needed
        messagebox.showinfo("Info", "Use Selected Transaction clicked.\n\nAuto-fill not yet implemented in this version.")

    def toggle_instructions(self):
        if self.instructions_frame.winfo_ismapped():
            self.instructions_frame.pack_forget()
            self.instructions_button.config(text="Show Instructions")
        else:
            self.instructions_frame.pack(anchor="w", pady=(0, 10))
            self.instructions_button.config(text="Hide Instructions")

    def set_dark_mode(self):
        self.dark_bg = "#1e1e1e"
        self.medium_gray = "#4a4a4a"
        self.dark_fg = "#e6e6e6"
        self.entry_bg = "#2b2b2b"
        self.entry_fg = "#ffffff"
        self.button_bg = "#3a3a3a"
        self.button_fg = "#ffffff"

        self.root.configure(bg=self.medium_gray)
        self.container.configure(bg=self.dark_bg)
        self.outer.configure(bg=self.dark_bg)
        self.canvas.configure(bg=self.dark_bg, highlightbackground=self.medium_gray, highlightthickness=2)
        self.scrollbar.configure(bg=self.dark_bg, troughcolor="#2b2b2b", activebackground="#3a3a3a", highlightbackground=self.medium_gray)

        for frame in [self.scrollable_frame, self.inputs_frame]:
            frame.configure(bg=self.dark_bg)

        self._recolor(self.scrollable_frame)

    def _recolor(self, widget):
        for child in widget.winfo_children():
            cls = child.__class__.__name__
            if cls == "Label":
                child.configure(bg=self.dark_bg, fg=self.dark_fg)
            elif cls == "Entry":
                child.configure(bg=self.entry_bg, fg=self.entry_fg, insertbackground=self.entry_fg)
            elif cls == "Text":
                child.configure(bg=self.entry_bg, fg=self.entry_fg, insertbackground=self.entry_fg)
            elif cls == "Button":
                child.configure(bg=self.button_bg, fg=self.button_fg, activebackground="#505050")
            elif cls == "Frame":
                child.configure(bg=self.dark_bg)
            self._recolor(child)

    def create_input_fields(self):
        for widget in self.inputs_frame.winfo_children():
            widget.destroy()

        try:
            count = int(self.num_inputs_entry.get().strip())
            if count < 1:
                raise ValueError
        except ValueError:
            messagebox.showerror("Input Error", "Number of inputs must be a positive integer.")
            return

        self.input_rows = []

        for i in range(count):
            row = {}

            tk.Label(self.inputs_frame, text=f"\nInput {i+1}").pack(anchor="w")

            tk.Label(self.inputs_frame, text="VOUT:").pack(anchor="w")
            row["vout"] = tk.Entry(self.inputs_frame, width=20)
            row["vout"].pack(anchor="w")

            tk.Label(self.inputs_frame, text="Input Amount (sats):").pack(anchor="w")
            row["amount"] = tk.Entry(self.inputs_frame, width=20)
            row["amount"].pack(anchor="w")

            tk.Label(self.inputs_frame, text="Bare Multisig scriptPubKey (hex):").pack(anchor="w")
            row["script"] = tk.Entry(self.inputs_frame, width=80)
            row["script"].pack(fill="x")

            self.input_rows.append(row)

        suggested_fee = 130 * count
        self.fee_entry.delete(0, tk.END)
        self.fee_entry.insert(0, str(suggested_fee))

        self._recolor(self.inputs_frame)

    def build_transaction(self):
        txid = self.txid_entry.get().strip()
        wif = self.wif_entry.get().strip()
        dest_addr = self.dest_entry.get().strip()

        if not txid or not wif or not dest_addr:
            messagebox.showerror("Input Error", "TXID, WIF, and Destination Address are all required.")
            return

        try:
            full = base58.b58decode_check(wif)
            privkey = full[1:33]
            sk = SigningKey.from_string(privkey, curve=SECP256k1)
        except Exception as e:
            messagebox.showerror("Invalid WIF", f"Could not decode private key:\n{e}")
            return

        try:
            dest_spk_hex = address_to_scriptpubkey(dest_addr)
        except Exception as e:
            messagebox.showerror("Invalid Address", f"Destination address error:\n{e}")
            return

        inputs = []
        total_input = 0

        if not hasattr(self, "input_rows") or not self.input_rows:
            messagebox.showerror("No Inputs", "Please create input fields first.")
            return

        for row in self.input_rows:
            try:
                vout = int(row["vout"].get().strip())
                amount = int(row["amount"].get().strip())
                script = row["script"].get().strip()
                if not script:
                    raise ValueError("Empty scriptPubKey")
                if vout < 0 or amount < 0:
                    raise ValueError("Amounts and VOUT must be non-negative")
            except ValueError as e:
                messagebox.showerror("Invalid Input Field", f"Input field error:\n{e}")
                return

            total_input += amount
            inputs.append({
                "vout": vout,
                "amount": amount,
                "script_pubkey": script
            })

        try:
            fee = int(self.fee_entry.get().strip())
            if fee <= 0:
                raise ValueError
        except ValueError:
            messagebox.showerror("Invalid Fee", "Fee must be a positive integer.")
            return

        if total_input < fee:
            messagebox.showerror("Insufficient Funds", "Total input is less than the fee.")
            return

        output_amount = total_input - fee

        version = struct.pack("<I", 1)
        locktime = struct.pack("<I", 0)
        sequence = b"\xff\xff\xff\xff"

        outputs = [{"amount": output_amount, "script_pubkey": dest_spk_hex}]

        outputs_ser = encode_varint(len(outputs))
        for o in outputs:
            out_value = struct.pack("<Q", o["amount"])
            out_script = bytes.fromhex(o["script_pubkey"])
            outputs_ser += out_value + encode_varint(len(out_script)) + out_script

        sigs = []
        for idx, inp in enumerate(inputs):
            txid_le = bytes.fromhex(txid)[::-1]
            script_code = bytes.fromhex(inp["script_pubkey"])

            preimage = version
            preimage += encode_varint(len(inputs))

            for j, other in enumerate(inputs):
                txid2 = bytes.fromhex(txid)[::-1]
                vout2 = struct.pack("<I", other["vout"])
                sc = script_code if j == idx else b""
                preimage += txid2 + vout2 + encode_varint(len(sc)) + sc + sequence

            preimage += outputs_ser
            preimage += locktime + struct.pack("<I", 1)

            sighash = dsha256(preimage)
            raw_sig = sk.sign_digest(sighash, sigencode=sigencode_der)
            sig = normalize_low_s(raw_sig) + b"\x01"
            sigs.append(sig)

        final = version
        final += encode_varint(len(inputs))

        for i, inp in enumerate(inputs):
            txid_le = bytes.fromhex(txid)[::-1]
            vout = struct.pack("<I", inp["vout"])
            script_sig = b"\x00" + bytes([len(sigs[i])]) + sigs[i]
            final += txid_le + vout + encode_varint(len(script_sig)) + script_sig + sequence

        final += outputs_ser + locktime

        self.hex_box.delete("1.0", tk.END)
        self.hex_box.insert(tk.END, final.hex())

        summary = (
            f"Transaction built successfully.\n\n"
            f"Total input: {total_input} sats\n"
            f"Fee: {fee} sats\n"
            f"Output amount: {output_amount} sats\n"
            f"Recipient: {dest_addr}"
        )
        messagebox.showinfo("Success", summary)

    def copy_hex(self):
        tx_hex = self.hex_box.get("1.0", tk.END).strip()
        if not tx_hex:
            messagebox.showerror("Nothing to Copy", "No transaction hex to copy.")
            return
        self.root.clipboard_clear()
        self.root.clipboard_append(tx_hex)
        messagebox.showinfo("Copied", "Transaction hex copied to clipboard.")

    # ============================
    # Run GUI
    # ============================

if __name__ == "__main__":
    root = tk.Tk()
    app = TxBuilderGUI(root)
    root.mainloop()
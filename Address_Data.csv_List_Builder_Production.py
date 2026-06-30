#!/usr/bin/env python3
"""
CSV_List_Builder_Production.py

Universal Bitcoin Core chainstate -> CSV (Address,Balance_satoshis,Balance_BTC,AddressType,Hash160)
Only P2PKH and P2WPKH addresses are included.
Aggregates UTXOs per address.
Performs an integrity check after aggregation.

Usage:
  python Haskat_List_Builder_Production.py [path/to/chainstate]
"""
from __future__ import annotations
import os, sys, time, csv, hashlib, traceback
from pathlib import Path
from decimal import Decimal, getcontext

try:
    import plyvel
except Exception:
    print("ERROR: plyvel (LevelDB Python bindings) not found. Install plyvel before running.")
    raise

# ---- Config ----
PRINT_EVERY = 1_000_000
INTEGRITY_PRINT_EVERY = 100_000
OUTPUT_FILE = "Hash_db_Full_25_09_2025_220pm.csv"
HRP = "bc"  # Bech32 human-readable part for mainnet
getcontext().prec = 28

# ---- Base58 / address utilities ----
BASE58_ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

def b58encode(b: bytes) -> str:
    n = int.from_bytes(b, "big")
    res = ""
    while n > 0:
        n, r = divmod(n, 58)
        res = BASE58_ALPHABET[r] + res
    leading = 0
    for c in b:
        if c == 0:
            leading += 1
        else:
            break
    return "1" * leading + res

def hash160_to_p2pkh(h160: bytes) -> str:
    payload = b"\x00" + h160
    checksum = hashlib.sha256(hashlib.sha256(payload).digest()).digest()[:4]
    return b58encode(payload + checksum)

# ---- Bech32 / segwit utilities ----
CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
GEN = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]

def bech32_polymod(values):
    chk = 1
    for v in values:
        top = chk >> 25
        chk = ((chk & 0x1ffffff) << 5) ^ v
        for i in range(5):
            if (top >> i) & 1:
                chk ^= GEN[i]
    return chk

def bech32_hrp_expand(hrp):
    return [ord(x) >> 5 for x in hrp] + [0] + [ord(x) & 31 for x in hrp]

def bech32_create_checksum(hrp, data, spec="bech32"):
    const = 1 if spec == "bech32" else 0x2bc830a3
    values = bech32_hrp_expand(hrp) + data
    polymod = bech32_polymod(values + [0]*6) ^ const
    return [(polymod >> (5 * (5 - i))) & 31 for i in range(6)]

def bech32_encode(hrp, data, spec="bech32"):
    checksum = bech32_create_checksum(hrp, data, spec)
    return hrp + "1" + "".join([CHARSET[d] for d in data + checksum])

def convertbits(data, frombits, tobits, pad=True):
    acc = 0; bits = 0; ret = []
    maxv = (1 << tobits) - 1
    for value in data:
        acc = (acc << frombits) | value
        bits += frombits
        while bits >= tobits:
            bits -= tobits
            ret.append((acc >> bits) & maxv)
    if pad and bits:
        ret.append((acc << (tobits - bits)) & maxv)
    return ret

def segwit_addr_encode(hrp, witver, witprog: bytes):
    spec = "bech32" if witver == 0 else "bech32m"
    data = [witver] + convertbits(list(witprog), 8, 5, pad=True)
    return bech32_encode(hrp, data, spec)

# ---- Deobfuscation ----
def find_obfuscation_key(db) -> bytes:
    v = db.get(b'\x0eobfuscate_key')
    if v:
        if len(v) >= 1 and v[0] == len(v) - 1:
            return v[1:]
        return v
    it = db.iterator()
    for i, (k, val) in enumerate(it):
        if not k: continue
        if b'obfuscate' in k or k == b'\x0eobfuscate_key':
            if val and val[0] == len(val) - 1:
                return val[1:]
            return val
        if i > 2000:
            break
    return b''

def deobfuscate_value(v: bytes, key: bytes) -> bytes:
    if not key:
        return v
    kl = len(key)
    return bytes([c ^ key[i % kl] for i, c in enumerate(v)])

# ---- Varint read ----
def read_varint_b128(bts: bytes, offset: int):
    parts = []
    while True:
        if offset >= len(bts):
            raise IndexError("varint read past end of buffer")
        b = bts[offset]; offset += 1
        cont = (b & 0x80) != 0
        part = b & 0x7f
        if cont:
            part += 1
        parts.append(part)
        if not cont:
            break
    val = 0
    for p in parts:
        val = (val << 7) | p
    return val, offset

# ---- Amount decompression ----
def decompress_amount(x: int) -> int:
    if x == 0: return 0
    x -= 1
    e = x % 10
    x //= 10
    n = 0
    if e < 9:
        d = (x % 9) + 1
        x //= 9
        n = x * 10 + d
    else:
        n = x + 1
    while e:
        n *= 10
        e -= 1
    return n

# ---- Script decompression ----
def decompress_script(v: bytes, offset: int, nSize: int):
    if nSize == 0:
        h160 = v[offset:offset+20]; offset += 20
        script = b'\x76\xa9\x14' + h160 + b'\x88\xac'
        return script, offset
    if nSize == 1:
        h160 = v[offset:offset+20]; offset += 20
        script = b'\xa9\x14' + h160 + b'\x87'
        return script, offset
    if nSize == 2 or nSize == 3:
        xcoord = v[offset:offset+32]; offset += 32
        pubkey = (b'\x02' if nSize == 2 else b'\x03') + xcoord
        script = bytes([len(pubkey)]) + pubkey + b'\xac'
        return script, offset
    if nSize == 4 or nSize == 5:
        xy = v[offset:offset+64]; offset += 64
        pubkey = b'\x04' + xy
        script = bytes([len(pubkey)]) + pubkey + b'\xac'
        return script, offset
    script_len = nSize - 6
    script = v[offset:offset+script_len]; offset += script_len
    return script, offset

# ---- Script -> address / type / hash160 ----
def scriptpubkey_to_address(script: bytes):
    L = len(script)
    if L == 25 and script[0:3] == b'\x76\xa9\x14' and script[-2:] == b'\x88\xac':
        h160 = script[3:23]
        return hash160_to_p2pkh(h160), "P2PKH", h160.hex()
    if L == 22 and script[0] == 0x00 and script[1] == 0x14:
        h160 = script[2:22]
        return segwit_addr_encode(HRP, 0, h160), "P2WPKH", h160.hex()
    return None, None, None

# ---- Parse single UTXO ----
def parse_utxo_value(vbytes: bytes, ob_key: bytes):
    data = deobfuscate_value(vbytes, ob_key)
    off = 0
    nCode, off = read_varint_b128(data, off)
    amount_comp, off = read_varint_b128(data, off)
    amount = decompress_amount(amount_comp)
    nSize, off = read_varint_b128(data, off)
    script, off = decompress_script(data, off, nSize)
    return amount, script

# ---- Safe BTC formatting helper ----
def format_btc_exact8(satoshis: int) -> str:
    d = Decimal(satoshis) / Decimal(100_000_000)
    # f-string with Decimal will produce decimal string; ensure 8 dp
    return f"{d:.8f}"

# ---- Integrity check ----
def integrity_check(balances_dict):
    csv_data = []
    total = len(balances_dict)
    ok_count = 0
    idx = 0

    print("\nStarting integrity check on unique addresses...")
    for addr, (bal, atype, h160) in balances_dict.items():
        idx += 1
        if not addr:
            continue
        valid = False
        try:
            if atype == "P2PKH":
                payload = b"\x00" + bytes.fromhex(h160)
                checksum = hashlib.sha256(hashlib.sha256(payload).digest()).digest()[:4]
                if b58encode(payload + checksum) == addr:
                    valid = True
            elif atype == "P2WPKH":
                if segwit_addr_encode(HRP, 0, bytes.fromhex(h160)) == addr:
                    valid = True
        except Exception:
            # log and continue
            # don't crash entire run because of one bad entry
            # optional: write to debug log
            # import traceback above and use if desired
            pass

        btc_str = format_btc_exact8(bal)
        csv_data.append([addr, str(bal), btc_str, atype, h160])
        if valid:
            ok_count += 1

        if idx % INTEGRITY_PRINT_EVERY == 0 or idx == total:
            pct = idx / total * 100 if total else 100.0
            print(f"Integrity check: {idx:,} / {total:,} ({pct:.2f}%)")
    print(f"Integrity_check complete: {ok_count}/{total} addresses OK")
    return csv_data

# ---- Main program ----
def main():
    if len(sys.argv) > 1 and not sys.argv[1].isdigit():
        chainstate_dir = sys.argv[1]
    else:
        if os.name == "nt":
            app = os.getenv("APPDATA", "")
            chainstate_dir = os.path.join(app, "Bitcoin", "chainstate")
        else:
            chainstate_dir = os.path.expanduser("~/.bitcoin/chainstate")

    print("Parsing chainstate from:", chainstate_dir)
    if not os.path.isdir(chainstate_dir):
        print("ERROR: chainstate directory not found:", chainstate_dir)
        sys.exit(1)

    db = plyvel.DB(chainstate_dir, compression=None)
    try:
        ob_key = find_obfuscation_key(db)
    except Exception as e:
        print("Failed reading obfuscation key:", e)
        ob_key = b""
    print("Obfuscation key:", ob_key.hex() if ob_key else "(none)")

    start_time = time.time()
    total_parsed = 0
    matched = 0
    balances = {}  # addr -> (satoshis, atype, h160_hex)
    total_balance = 0

    try:
        for k, v in db:
            if not k:
                continue
            first = k[0]
            if first != 0x43 and first != 0x63:
                continue
            total_parsed += 1
            try:
                amount, script = parse_utxo_value(v, ob_key)
                addr, atype, h160 = scriptpubkey_to_address(script)
                if addr is not None and atype in ["P2PKH","P2WPKH"]:
                    matched += 1
                    total_balance += amount
                    if addr in balances:
                        prev_bal, prev_type, prev_h = balances[addr]
                        balances[addr] = (prev_bal + amount, prev_type, prev_h)
                    else:
                        balances[addr] = (amount, atype, h160)
            except Exception as e:
                # print warning but continue parsing; helpful for debugging intermittent issues
                print(f"[Warning] Failed parsing UTXO key={k.hex()[:32]}...: {e}")
                # optionally: log stacktrace
                # traceback.print_exc()
            if total_parsed % PRINT_EVERY == 0:
                elapsed = time.time() - start_time
                speed = int(total_parsed / max(1e-6, elapsed))
                print(f"Processed {total_parsed:,} | matched {matched:,} | unique {len(balances):,} | speed {speed:,}/s | total_balance: {total_balance:,} sats")
    except KeyboardInterrupt:
        print("\nInterrupted by user — proceeding with partial results...")

    db.close()

    # ---- Run integrity check ----
    print("\nStarting integrity check on unique addresses...")
    csv_data = integrity_check(balances)

    # ---- Write CSV ----
    print(f"\nWriting CSV ({len(csv_data):,} unique addresses)...")
    with open(OUTPUT_FILE, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["Address","Balance_satoshis","Balance_BTC","AddressType","Hash160"])
        for row in csv_data:
            writer.writerow(row)

    elapsed = time.time() - start_time
    print("\n========== Parsing Summary ==========")
    print(f"Total UTXOs parsed : {total_parsed:,}")
    print(f"Total matched UTXOs: {matched:,}")
    print(f"Unique addresses    : {len(balances):,}")
    # counts per address type
    addr_type_counts = {}
    for _, (s, t, h) in balances.items():
        addr_type_counts[t] = addr_type_counts.get(t, 0) + 1
    print("Address type counts :")
    for t, c in sorted(addr_type_counts.items(), key=lambda x: (-x[1], x[0])):
        print(f"  {t:<8}: {c:,}")
    print(f"Total balance (sats): {total_balance:,}")
    print(f"Output CSV file     : {Path(OUTPUT_FILE).resolve()}")
    print(f"Elapsed time        : {int(elapsed//3600)}h {int((elapsed%3600)//60)}m {int(elapsed%60)}s")
    print("====================================")
    input("Press 'c' to close...")

# ---- Utility to get hash160 from final address (kept for compatibility) ----
def addr_to_hash160(addr: str, bech32=False) -> str:
    if addr.startswith("1") and not bech32:
        b = b58decode(addr)
        return b[1:-4].hex()
    elif addr.startswith(HRP+"1") and bech32:
        return bech32_decode_hash160(addr).hex()
    return ""

def b58decode(s: str) -> bytes:
    n = 0
    for c in s:
        n *= 58
        n += BASE58_ALPHABET.index(c)
    h = n.to_bytes((n.bit_length() + 7)//8, 'big')
    leading = 0
    for c in s:
        if c == '1': leading += 1
        else: break
    return b'\x00'*leading + h

def bech32_decode_hash160(addr: str) -> bytes:
    addr = addr.lower()
    hrp, data = addr.split('1')
    data = [CHARSET.index(c) for c in data]
    decoded = convertbits(data[1:-6], 5, 8, pad=False)
    return bytes(decoded)

if __name__ == "__main__":
    main()

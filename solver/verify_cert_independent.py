#!/usr/bin/env python3
"""
verify_cert_independent.py - Zero-dependency pure-Python exact arbitrary-precision verifier
for Caccetta-Haggkvist Q-SOS Flag Algebra certificates.

Mirrors the exact integer arithmetic that Lean 4 will verify:
1. Reads raw unlabeled models M_m and exact integer triplet tables from flags_m<m>.bin.
2. Reads exact integer Q-SOS certificate JSON (c_num/c_den, lam_int, sos_types[t].factors = [(w_j, u_j)]).
3. Asserts every SOS weight w_j > 0 (so Q_sigma = sum_j w_j u_j u_j^T is PSD by construction!).
4. Asserts c_den > 0, and if mode == 'ge', asserts every lam_int[F] >= 0.
5. Computes S_num[H] = lcm_denom * q_denom * S(H) in exact arbitrary-precision Python int
   for EVERY model H in M_m and asserts S_num[H] < 0 for ALL H!
"""

import argparse
import json
import math
import struct
import sys
import time
from fractions import Fraction

from exact_certificate import gram_matrix, integer, read_records, require


def verify_certificate(bin_path: str, cert_path: str, mode: str = "eq") -> bool:
    t0 = time.monotonic()
    with open(cert_path, "r") as f:
        cert = json.load(f)

    m = cert["m"]
    c_num = integer(cert["c_num"])
    c_den = integer(cert["c_den"])
    require(c_den > 0 and c_num > 0, "invalid degree ratio")
    require(mode in ("eq", "ge"), "unknown out-degree mode")
    q_denom = integer(cert["q_denom"])
    lam_scale = integer(cert["lam_scale"])
    require(q_denom > 0 and lam_scale == q_denom, "inconsistent coefficient scales")

    with open(bin_path, "rb") as f:
        magic, bm, nM = struct.unpack("<iii", f.read(12))
        require((magic, bm, nM) == (0x464C4147, m, cert["num_models"]), "flag table header mismatch")
        f.seek(8 * nM, 1)  # skip model codes

        (num_types,) = struct.unpack("<i", f.read(4))
        require(num_types == len(cert["sos_types"]), "SOS block count mismatch")

        types_raw = []
        for ti in range(num_types):
            k, ell, sigma_code, nf = struct.unpack("<iiQi", f.read(20))
            f.seek(8 * nf, 1)  # skip flag codes
            (naut,) = struct.unpack("<i", f.read(4))
            f.seek(4 * naut * nf, 1)  # skip auts
            denom, nnz = struct.unpack("<qq", f.read(16))
            raw_bytes = read_records(f, nnz, 16)
            types_raw.append((k, ell, sigma_code, nf, denom, nnz, raw_bytes))

        (nf1_2,) = struct.unpack("<i", f.read(4))
        f1_2 = struct.unpack(f"<{nf1_2}Q", f.read(8 * nf1_2))
        idx_eplus = f1_2.index(1)

        (nf1_m1,) = struct.unpack("<i", f.read(4))
        f.seek(8 * nf1_m1, 1)

        p1_denom, p1_nnz = struct.unpack("<qq", f.read(16))
        p1_bytes = read_records(f, p1_nnz, 16)

        u1_denom, u1_nnz = struct.unpack("<qq", f.read(16))
        u1_bytes = read_records(f, u1_nnz, 16)

    # Compute exact LCM denominator
    require(p1_denom > 0 and u1_denom > 0, "nonpositive degree denominator")
    lcm_d = math.lcm(p1_denom, u1_denom * c_den)
    for t in types_raw:
        require(t[4] > 0, "nonpositive SOS table denominator")
        lcm_d = math.lcm(lcm_d, t[4])

    lam_int = [integer(x) for x in cert["lam_int"]]
    require(len(lam_int) == nf1_m1, "out-degree multiplier count mismatch")
    if mode == "ge":
        require(all(x >= 0 for x in lam_int), "negative multiplier in ge mode")

    S_num = [0] * nM

    # 1. Exact linear out-degree terms: lam_F * ([[E+ * F]]_1(H) - (c_num/c_den) [[F]]_1(H))
    mult_p1 = lcm_d // p1_denom
    for h, a, b, cnt in struct.iter_unpack("<iiii", p1_bytes):
        if a == idx_eplus:
            lv = lam_int[b]
            if lv:
                S_num[h] += lv * cnt * mult_p1

    mult_u1 = (lcm_d // (u1_denom * c_den)) * c_num
    for h, a, b, cnt in struct.iter_unpack("<iiii", u1_bytes):
        lv = lam_int[a]
        if lv:
            S_num[h] -= lv * cnt * mult_u1

    # 2. Exact PSD SOS terms: sum_j w_j * (u_j^T M^sigma(H) u_j), strictly verifying w_j > 0!
    total_factors = 0
    for ti, st in enumerate(cert["sos_types"]):
        k, ell, sigma_code, nf, denom, nnz, raw_bytes = types_raw[ti]
        require((st["k"], st["ell"], st["sigma_code"], st["denom"]) == (k, ell, sigma_code, denom),
                f"flag type mismatch in block {ti}")
        factors = st["factors"]
        Q_int = gram_matrix(factors, nf)
        if Q_int is None:
            continue
        total_factors += len(factors)
        mult_t = lcm_d // denom

        for h, a, b, cnt in struct.iter_unpack("<iiii", raw_bytes):
            qab = Q_int[a][b]
            if qab:
                S_num[h] += cnt * mult_t * qab

    max_val = max(S_num)
    min_val = min(S_num)
    bad = [h for h, v in enumerate(S_num) if v >= 0]
    elapsed = time.monotonic() - t0

    print(f"[INDEPENDENT EXACT VERIFIER] m={m}, c={c_num}/{c_den} ({c_num/c_den:.7f}), mode={mode}")
    print(f"  models checked: {nM}, total SOS rank: {total_factors}")
    print(f"  max S(H) = {Fraction(max_val, lcm_d * q_denom)} ({max_val / (lcm_d * q_denom):.6e})")
    print(f"  min S(H) = {min_val / (lcm_d * q_denom):.6e}")
    print(f"  violations (S(H) >= 0): {len(bad)}/{nM}  (verified in {elapsed:.2f}s)")
    if bad:
        print(f"  FAILED! First bad models: {bad[:10]}")
        return False
    print("  >>> VERIFIED 100% EXACTLY!! <<<")
    return True


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Verify a rational flag certificate.")
    parser.add_argument("flags_bin")
    parser.add_argument("cert_json")
    parser.add_argument("mode", nargs="?", choices=("eq", "ge"), default="eq")
    args = parser.parse_args()
    sys.exit(0 if verify_certificate(args.flags_bin, args.cert_json, args.mode) else 1)

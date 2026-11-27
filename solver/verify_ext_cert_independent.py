#!/usr/bin/env python3
"""
verify_ext_cert_independent.py - Zero-dependency pure-Python arbitrary-precision exact integer
verifier for Class 1-4 (Out-Reg + CS + Generalized Induction + CSS/CKLS, lin+SOS) TWO-ENDPOINT
interval certificates!

Verifies BOTH endpoints c_low and c_high strictly < 0 for ALL H in M_m, proving by affine
linearity S_H(c) = U_H + c*V_H that S_H(c) <= -delta < 0 for EVERY c in [c_low, c_high]!
Asserts every SOS weight w_j > 0 and every Induction/CSS multiplier mu_i > 0!
"""

import argparse
import json
import math
import struct
import sys
import time
from fractions import Fraction

from exact_certificate import gram_matrix, integer, read_records, require


def verify_ext_cert(flags_bin: str, ext_bin: str, cert_json: str) -> bool:
    t0 = time.monotonic()
    with open(cert_json, "r") as f:
        cert = json.load(f)

    m = integer(cert["m"])
    nM = integer(cert["num_models"])
    c_low = Fraction(integer(cert["c_low_num"]), integer(cert["c_low_den"]))
    c_high = Fraction(integer(cert["c_high_num"]), integer(cert["c_high_den"]))
    alpha = Fraction(integer(cert["alpha_num"]), integer(cert["alpha_den"]))
    require(0 < c_low <= c_high and alpha > 0, "invalid degree interval or CSS coefficient")

    use_ind = bool(cert["use_ind"])
    use_css = bool(cert["use_css"])
    use_sos_ind = bool(cert["use_sos_ind"])
    use_sos_css = bool(cert["use_sos_css"])
    r_fracs = [Fraction(integer(a), integer(b)) for a, b in cert["r_fracs"]]
    r_sos_fracs = [Fraction(integer(a), integer(b)) for a, b in cert["r_sos_fracs"]]
    require(all(r >= 0 for r in r_fracs + r_sos_fracs), "negative CSS tangent")
    q_denom = integer(cert["q_denom"])
    require(q_denom > 0, "nonpositive coefficient denominator")

    # Read flags_m<m>.bin
    with open(flags_bin, "rb") as f:
        magic, bm, bnM = struct.unpack("<iii", f.read(12))
        require((magic, bm, bnM) == (0x464C4147, m, nM), "flag table header mismatch")
        f.seek(8 * nM, 1)
        (n_base,) = struct.unpack("<i", f.read(4))
        base_types = []
        for _ in range(n_base):
            k, ell, sc, nf = struct.unpack("<iiQi", f.read(20))
            f.seek(8 * nf, 1)
            (naut,) = struct.unpack("<i", f.read(4))
            f.seek(4 * naut * nf, 1)
            denom, nnz = struct.unpack("<qq", f.read(16))
            raw = read_records(f, nnz, 16)
            base_types.append((nf, denom, raw))

        (nf1_2,) = struct.unpack("<i", f.read(4))
        f1_2 = struct.unpack(f"<{nf1_2}Q", f.read(8 * nf1_2))
        idx_eplus = f1_2.index(1)
        (nf1_m1,) = struct.unpack("<i", f.read(4))
        f.seek(8 * nf1_m1, 1)
        p1_denom, p1_nnz = struct.unpack("<qq", f.read(16))
        p1_bytes = read_records(f, p1_nnz, 16)
        u1_denom, u1_nnz = struct.unpack("<qq", f.read(16))
        u1_bytes = read_records(f, u1_nnz, 16)

    # Read ext_m<m>.bin
    with open(ext_bin, "rb") as f:
        magic, em, enM = struct.unpack("<iii", f.read(12))
        require((magic, em, enM) == (0x45585446, m, nM), "extension table header mismatch")

        (n_ind,) = struct.unpack("<i", f.read(4))
        ind_fams = []
        for _ in range(n_ind):
            tau_k, tau_code, k_orig, is_lifted, nf = struct.unpack("<iQiii", f.read(24))
            f.seek(8 * nf, 1)
            denom, nnz = struct.unpack("<qq", f.read(16))
            raw = read_records(f, nnz, 20)
            ind_fams.append((nf, denom, raw))

        (n_css,) = struct.unpack("<i", f.read(4))
        css_fams = []
        for _ in range(n_css):
            tau_k, tau_code, k_orig, is_lifted, nf = struct.unpack("<iQiii", f.read(24))
            f.seek(8 * nf, 1)
            denom, nnz = struct.unpack("<qq", f.read(16))
            raw = read_records(f, nnz, 20)
            css_fams.append((nf, denom, raw))

        (n_sos_ind,) = struct.unpack("<i", f.read(4))
        sos_ind_fams = []
        for _ in range(n_sos_ind):
            tau_k, tau_code, k_orig, is_lifted, ell, nf = struct.unpack("<iQiiii", f.read(28))
            f.seek(8 * nf, 1)
            (naut,) = struct.unpack("<i", f.read(4))
            f.seek(4 * naut * nf, 1)
            denom, nnz = struct.unpack("<qq", f.read(16))
            raw = read_records(f, nnz, 24)
            sos_ind_fams.append((nf, denom, raw))

        (n_sos_css,) = struct.unpack("<i", f.read(4))
        sos_css_fams = []
        for _ in range(n_sos_css):
            tau_k, tau_code, k_orig, is_lifted, ell, nf = struct.unpack("<iQiiii", f.read(28))
            f.seek(8 * nf, 1)
            (naut,) = struct.unpack("<i", f.read(4))
            f.seek(4 * naut * nf, 1)
            denom, nnz = struct.unpack("<qq", f.read(16))
            raw = read_records(f, nnz, 24)
            sos_css_fams.append((nf, denom, raw))

    lam_int = [integer(x) for x in cert["lam_int"]]
    require(len(lam_int) == nf1_m1, "out-degree multiplier count mismatch")
    mu_int = [0] * integer(cert["mu_len"])
    for idx, val in cert["mu_sparse"]:
        i, v = integer(idx), integer(val)
        require(0 <= i < len(mu_int) and not mu_int[i], f"invalid or repeated multiplier index {i}")
        require(v > 0, f"nonpositive multiplier at {i}")
        mu_int[i] = v

    require(len(cert["sos_base"]) == len(base_types), "base SOS block count mismatch")
    Q_base = [gram_matrix(factors, nf) for factors, (nf, _, _) in zip(cert["sos_base"], base_types)]
    ext_nfs = []
    if use_sos_ind:
        ext_nfs.extend([f[0] for f in sos_ind_fams])
    if use_sos_css:
        for f in sos_css_fams:
            for _ in r_sos_fracs:
                ext_nfs.append(f[0])
    require(len(cert["sos_ext"]) == len(ext_nfs), "weighted SOS block count mismatch")
    Q_ext = [gram_matrix(factors, nf) for factors, nf in zip(cert["sos_ext"], ext_nfs)]

    def eval_at(c_frac: Fraction):
        denoms = [p1_denom, u1_denom * c_frac.denominator] + [t[1] for t in base_types]
        if use_ind:
            denoms.extend([f[1] * c_frac.denominator for f in ind_fams])
        if use_css:
            for f in css_fams:
                denoms.append(f[1] * alpha.denominator)
                for rf in r_fracs:
                    denoms.append(f[1] * rf.denominator * rf.denominator * c_frac.denominator)
        if use_sos_ind:
            denoms.extend([f[1] * c_frac.denominator for f in sos_ind_fams])
        if use_sos_css:
            for f in sos_css_fams:
                denoms.append(f[1] * alpha.denominator)
                for rf in r_sos_fracs:
                    denoms.append(f[1] * rf.denominator * rf.denominator * c_frac.denominator)
        require(all(d > 0 for d in denoms), "nonpositive table denominator")
        lcm_d = 1
        for d in denoms:
            lcm_d = math.lcm(lcm_d, d)

        S = [0] * nM
        mp1 = lcm_d // p1_denom
        for h, a, b, cnt in struct.iter_unpack("<iiii", p1_bytes):
            if a == idx_eplus:
                lv = lam_int[b]
                if lv:
                    S[h] += lv * cnt * mp1
        mu1 = (lcm_d // (u1_denom * c_frac.denominator)) * c_frac.numerator
        for h, a, b, cnt in struct.iter_unpack("<iiii", u1_bytes):
            lv = lam_int[a]
            if lv:
                S[h] -= lv * cnt * mu1

        off = 0
        cn, cd = c_frac.numerator, c_frac.denominator
        if use_ind:
            for nf, d0, raw in ind_fams:
                sub = mu_int[off : off + nf]; off += nf
                if not any(sub):
                    continue
                m_ss = lcm_d // d0
                m_c = (lcm_d // (d0 * cd)) * cn
                for h, fi, css, cf0, cone in struct.iter_unpack("<iiiii", raw):
                    mv = sub[fi]
                    if mv:
                        S[h] += mv * (css * m_ss + (cf0 - cone) * m_c)

        if use_css:
            an, ad = alpha.numerator, alpha.denominator
            for nf, d0, raw in css_fams:
                m_chi = (lcm_d // (d0 * ad)) * an
                for rf in r_fracs:
                    sub = mu_int[off : off + nf]; off += nf
                    if not any(sub):
                        continue
                    rn, rd = rf.numerator, rf.denominator
                    m_ss = (lcm_d // (d0 * rd)) * (2 * rn)
                    m_one = (lcm_d // (d0 * rd * rd)) * (rn * rn) - (lcm_d // (d0 * rd * cd)) * (2 * rn * cn)
                    for h, fi, cchi, css, cone in struct.iter_unpack("<iiiii", raw):
                        mv = sub[fi]
                        if mv:
                            S[h] += mv * (cchi * m_chi + css * m_ss + cone * m_one)
        require(off == len(mu_int), "linear multiplier count mismatch")

        for (nf, d0, raw), Q in zip(base_types, Q_base):
            if Q is None:
                continue
            mt = lcm_d // d0
            for h, a, b, cnt in struct.iter_unpack("<iiii", raw):
                qab = Q[a][b]
                if qab:
                    S[h] += cnt * mt * qab

        ei = 0
        if use_sos_ind:
            for nf, d0, raw in sos_ind_fams:
                Q = Q_ext[ei]; ei += 1
                if Q is None:
                    continue
                m_ss = lcm_d // d0
                m_c = (lcm_d // (d0 * cd)) * cn
                for h, a, b, css, cf0, cone in struct.iter_unpack("<iiiiii", raw):
                    qab = Q[a][b]
                    if qab:
                        S[h] += qab * (css * m_ss + (cf0 - cone) * m_c)

        if use_sos_css:
            an, ad = alpha.numerator, alpha.denominator
            for nf, d0, raw in sos_css_fams:
                m_chi = (lcm_d // (d0 * ad)) * an
                for rf in r_sos_fracs:
                    Q = Q_ext[ei]; ei += 1
                    if Q is None:
                        continue
                    rn, rd = rf.numerator, rf.denominator
                    m_ss = (lcm_d // (d0 * rd)) * (2 * rn)
                    m_one = (lcm_d // (d0 * rd * rd)) * (rn * rn) - (lcm_d // (d0 * rd * cd)) * (2 * rn * cn)
                    for h, a, b, cchi, css, cone in struct.iter_unpack("<iiiiii", raw):
                        qab = Q[a][b]
                        if qab:
                            S[h] += qab * (cchi * m_chi + css * m_ss + cone * m_one)
        require(ei == len(Q_ext), "unused weighted SOS blocks")

        bad = sum(1 for v in S if v >= 0)
        return Fraction(max(S), lcm_d * q_denom), bad

    max_lo, bad_lo = eval_at(c_low)
    max_hi, bad_hi = eval_at(c_high)
    elapsed = time.monotonic() - t0
    print(f"[INDEPENDENT EXT EXACT VERIFIER] m={m}, interval=[{c_low}, {c_high}] ([{float(c_low):.6f}, {float(c_high):.6f}]), alpha={alpha}")
    print(f"  models={nM}, rank={cert['rank_base']}+{cert['rank_ext']}, nnz_mu={len(cert['mu_sparse'])}, q_denom={q_denom}")
    print(f"  endpoint c_low  = {c_low}: max S(H) = {max_lo} ({float(max_lo):.6e}), violations = {bad_lo}/{nM}")
    print(f"  endpoint c_high = {c_high}: max S(H) = {max_hi} ({float(max_hi):.6e}), violations = {bad_hi}/{nM}")
    print(f"  verified in {elapsed:.2f}s")
    if bad_lo == 0 and bad_hi == 0:
        print("  >>> 100% EXACT TWO-ENDPOINT INTERVAL CERTIFICATE VERIFIED!! <<<")
        return True
    print("  >>> VERIFICATION FAILED! <<<")
    return False


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Verify both endpoints against freshly generated flag tables.")
    parser.add_argument("flags_bin")
    parser.add_argument("ext_bin")
    parser.add_argument("cert_json")
    args = parser.parse_args()
    sys.exit(0 if verify_ext_cert(args.flags_bin, args.ext_bin, args.cert_json) else 1)

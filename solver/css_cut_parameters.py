#!/usr/bin/env python3
"""Test rational parameters for the feedback-arc cut argument in PROOF.md §3.2."""

import argparse
from fractions import Fraction


def cut_parameters(alpha, mix, quadratic, split, caps=None):
    if not (0 < alpha < 1 and 0 < mix <= 1 and 0 < quadratic < 1 and split >= 1):
        raise ValueError("expected 0 < alpha, quadratic < 1, 0 < mix <= 1 and split >= 1")
    u = 1 / alpha
    mu = u - 1
    pivot = mix / (4 * mu)
    slope = (4 - 3 * mix - mix * mu) / (4 * mu)
    balanced = u**2 * (split + 1)**2 / (16 * quadratic * split)
    unbalanced = u**2 / (4 * quadratic * split)
    penalized = max(0, u - split + 1)**2 / (4 * quadratic * split)
    required = (balanced, unbalanced, penalized)
    if caps is None:
        caps = required
    elif any(cap < need for cap, need in zip(caps, required)):
        raise ValueError("a supplied cap is smaller than its completed-square bound")
    cu, cw, cw1 = caps
    h = (1 - quadratic) * slope
    x1, x2 = (3 + mu) / 4, (2 + mu) / 2
    # Lower bounds after eliminating t1 >= 0 and t3 >= m3 >= 0.
    t1_slack = h - x1
    m3_slack = h + 2 * (cw - cw1) - u
    # If h >= x2, t2 >= 0 suffices. Otherwise use t2 <= a(1-a).
    cross = Fraction(1, 2) + min(0, h - x2)
    a2 = Fraction(1, 4) - cross
    a1 = cw - cu + cross
    a0 = (1 - quadratic) * pivot - cw
    points = [Fraction(0), Fraction(1)]
    if a2 > 0 and 0 < -a1 < 2 * a2:
        points.append(-a1 / (2 * a2))
    minimum, at = min((a0 + a * (a1 + a2*a), a) for a in points)
    return caps, t1_slack, m3_slack, minimum, at


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("alpha", nargs="?", type=Fraction, default=Fraction(1037, 1250))
    parser.add_argument("--mix", type=Fraction, default=Fraction(57, 67))
    parser.add_argument("--quadratic", type=Fraction, default=Fraction(14, 29))
    parser.add_argument("--split", type=Fraction, default=Fraction(3, 2))
    parser.add_argument("--caps", nargs=3, type=Fraction, metavar=("CU", "CW", "CW1"),
                        help="upper bounds for the three completed squares")
    args = parser.parse_args()
    try:
        caps, t1, m3, margin, at = cut_parameters(args.alpha, args.mix, args.quadratic, args.split, args.caps)
    except ValueError as error:
        parser.error(str(error))
    print("Completed-square caps:", *(str(cap) for cap in caps))
    print(f"Cut coefficient slacks: {t1}, {m3}")
    print(f"Minimum on [0,1]: {margin} at {at}")
    if t1 < 0 or m3 < 0 or margin <= 0:
        raise SystemExit("These parameters do not close the cut inequalities.")


if __name__ == "__main__":
    main()

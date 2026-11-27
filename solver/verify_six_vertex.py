#!/usr/bin/env python3
"""Evaluate a six-vertex interval certificate directly on all vertex orderings.

The two binary files supply flag identifiers and block order. Skip every stored
product count. Reconstruct both flag products and localizers from adjacency.
"""

import argparse
import itertools
import json
import math
import struct
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from fractions import Fraction
from pathlib import Path

from exact_certificate import integer, require


def decode(n, code):
    matrix = [[0] * n for _ in range(n)]
    for i, j in itertools.combinations(range(n), 2):
        code, trit = divmod(code, 4)
        require(trit < 3, "invalid oriented edge")
        matrix[i][j] = trit
        matrix[j][i] = (0, 2, 1)[trit]
    require(code == 0, "bits outside graph")
    return matrix


def file_code(graph, order):
    return sum(graph[i][j] << (2 * bit)
               for bit, (i, j) in enumerate(itertools.combinations(order, 2)))


def checked_models(path):
    """Inductively cover every extension by a directed triangle or a listed image."""
    data = json.loads(Path(path).read_bytes())
    prev = [0]
    require(data["models"]["1"] == prev, "incorrect one-vertex model")
    for n in range(2, 7):
        models = data["models"][str(n)]
        rows = data["steps"][str(n)]
        width = 3 ** (n - 1)
        require(len(rows) == width * len(prev), "incomplete extension witnesses")
        vertices = list(range(n))
        for i, code in enumerate(prev):
            base = decode(n - 1, code)
            for ext in range(width):
                tag, index, *rest = rows[i * width + ext]
                digits = [(ext // 3**j) % 3 for j in range(n - 1)]
                if tag == 0:
                    u, v = index, rest[0]
                    require(len(rest) == 1 and 0 <= u < n-1 and 0 <= v < n-1 and
                            base[u][v] == 1 and digits[v] == 1 and digits[u] == 2,
                            "invalid triangle witness")
                else:
                    require(tag == 1 and sorted(rest) == vertices and 0 <= index < len(models),
                            "invalid relabeling witness")
                    graph = [row + [d] for row, d in zip(base, digits)]
                    graph.append([(0, 2, 1)[d] for d in digits] + [0])
                    require(file_code(graph, rest) == models[index], "wrong extension image")
        prev = models
    require(len(prev) == 6583, "incorrect six-vertex list length")
    return prev


def unpack(stream, fields):
    fmt = struct.Struct("<" + fields)
    return fmt.unpack(stream.read(fmt.size))


def flag_list(stream, count):
    return unpack(stream, f"{count}Q")


def skip_counts(stream, record_size):
    _, count = unpack(stream, "qq")
    require(count >= 0, "negative table length")
    stream.seek(count * record_size, 1)


def flag_ids(flags, ext):
    with open(flags, "rb") as stream:
        require(unpack(stream, "iii") == (0x464C4147, 6, 6583), "wrong flag header")
        stream.seek(8 * 6583, 1)
        base = []
        for _ in range(unpack(stream, "i")[0]):
            k, size, sigma, count = unpack(stream, "iiQi")
            base.append((k, k, size, sigma, flag_list(stream, count)))
            stream.seek(4 * count * unpack(stream, "i")[0], 1)
            skip_counts(stream, 16)
        flag_list(stream, unpack(stream, "i")[0])
        degree = flag_list(stream, unpack(stream, "i")[0])
    families = []
    with open(ext, "rb") as stream:
        require(unpack(stream, "iii") == (0x45585446, 6, 6583), "wrong extension header")
        for weighted, extras in ((False, 1), (False, 2), (True, 1), (True, 2)):
            blocks = []
            for _ in range(unpack(stream, "i")[0]):
                k, sigma, orig, _ = unpack(stream, "iQii")
                size = unpack(stream, "i")[0] if weighted else 6 - extras
                count, = unpack(stream, "i")
                blocks.append((k, orig, size, sigma, flag_list(stream, count)))
                if weighted:
                    stream.seek(4 * count * unpack(stream, "i")[0], 1)
                skip_counts(stream, 24 if weighted else 20)
            families.append(blocks)
    return degree, base, *families


def pair_shift(i, j):
    # Column-major packing makes each initial vertex segment a bit prefix.
    return j * (j - 1) + 2 * i


def embed(graph, order, positions):
    return sum(graph[order[i]][order[j]] << pair_shift(positions[i], positions[j])
               for i, j in itertools.combinations(range(len(positions)), 2))


def make_terms(cert, metadata):
    degree, base, ind, css, sos_ind, sos_css = metadata
    alpha = Fraction(integer(cert["alpha_num"]), integer(cert["alpha_den"]))
    require(alpha >= Fraction(1037, 1250), "the CSS theorem must cover the chosen coefficient")
    tangents = [Fraction(integer(a), integer(b)) for a, b in cert["r_fracs"]]
    weighted_tangents = [Fraction(integer(a), integer(b)) for a, b in cert["r_sos_fracs"]]
    require(all(r >= 0 for r in tangents + weighted_tangents), "negative tangent")
    scale = math.lcm(alpha.denominator, *(r.denominator**2 for r in tangents + weighted_tangents))
    normalizer = scale * integer(cert["q_denom"])
    require(normalizer > 0, "nonpositive scale")

    # A table key consists of exactly the edges inside its one or two flags.
    # Roots overlap. Free vertex sets on the two sides of a product are disjoint.
    tables = {}
    loss = 0

    def add_block(family, kind, coefficients, weighted=False, tangent=None):
        nonlocal loss
        k, orig, size, sigma, flags = family
        root = decode(k, sigma)
        require(0 <= orig <= k <= size <= 6, "invalid flag size")
        if kind in ("ind", "css"):
            sink = any(all(i == v or root[i][v] == 1 for i in range(orig)) for v in range(orig))
            witness = any(all(root[i][v] == 1 for i in range(orig)) for v in range(orig, k))
            require(sink or witness, "missing sink or common out-neighbor")
        left = tuple(range(size))
        right = (*range(k), *range(size, size + size - k)) if weighted else ()
        used = {pair_shift(i, j) for side in (left, right) for i, j in itertools.combinations(side, 2)}
        mask = sum(3 << shift for shift in used)
        free_end = size + (size - k if weighted else 0)
        extras = {"degree": 1, "base": 0, "ind": 1, "css": 2}[kind]
        require(free_end + extras == 6, "flag and localizer must use six positions")
        layout = (kind, orig if kind in ("ind", "css") else 0, mask)
        table = tables.setdefault(layout, {})
        # Partial graph words for every representative, keeping all roots fixed.
        suffix_orders = [tuple(range(k)) + p for p in itertools.permutations(range(k, size))]
        words = []
        seen = set()
        for code in flags:
            graph = decode(size, code)
            require(file_code(graph, range(k)) == sigma, "flag has incorrect root type")
            left_words = {embed(graph, p, left) for p in suffix_orders}
            require(seen.isdisjoint(left_words), "two flag indices represent the same labeled flag")
            seen.update(left_words)
            right_words = {embed(graph, p, right) for p in suffix_orders} if weighted else set()
            words.append((left_words, right_words))
        if weighted:
            # Build the dot products directly from the published rank-one factors.
            factors = [(integer(f["w"]), [integer(x) for x in f["u"]]) for f in coefficients]
            require(all(w > 0 and len(v) == len(flags) for w, v in factors), "invalid SOS factor")
            if kind == "ind":
                loss += sum(w * max(map(abs, v))**2 for w, v in factors)
            entries = ((a, b, sum(w * v[a] * v[b] for w, v in factors))
                       for a in range(len(flags)) for b in range(len(flags)))
        else:
            require(len(coefficients) == len(flags), "incorrect linear multiplier count")
            if kind == "ind":
                loss += sum(coefficients)
            entries = ((a, a, val) for a, val in enumerate(coefficients))
        if kind == "css":
            chi, src, const = (int(scale * x) for x in (alpha, 2*tangent, tangent**2))
        for a, b, value in entries:
            if not value:
                continue
            for lword in words[a][0]:
                for rword in words[b][1] if weighted else (0,):
                    key = lword | rword
                    if kind == "css":
                        x, y, z = table.get(key, (0, 0, 0))
                        table[key] = (x + value*chi, y + value*src, z + value*const)
                    else:
                        table[key] = table.get(key, 0) + value*scale

    add_block((1, 1, 5, 0, degree), "degree", list(map(integer, cert["lam_int"])))
    require(len(base) == len(cert["sos_base"]), "base block count mismatch")
    for family, factors in zip(base, cert["sos_base"]):
        if factors:
            add_block(family, "base", factors, weighted=True)

    mu = [0] * integer(cert["mu_len"])
    for idx, val in cert["mu_sparse"]:
        i, v = integer(idx), integer(val)
        require(0 <= i < len(mu) and v > 0 and mu[i] == 0, "invalid linear multiplier")
        mu[i] = v
    offset = 0
    for active, families, kind, rs in ((cert["use_ind"], ind, "ind", [None]),
                                       (cert["use_css"], css, "css", tangents)):
        if active:
            for family in families:
                for r in rs:
                    end = offset + len(family[-1])
                    require(end <= len(mu), "missing linear multipliers")
                    if any(mu[offset:end]):
                        add_block(family, kind, mu[offset:end], tangent=r)
                    offset = end
    require(offset == len(mu), "unused linear multipliers")

    blocks = []
    if cert["use_sos_ind"]:
        blocks.extend((f, "ind", None) for f in sos_ind)
    if cert["use_sos_css"]:
        blocks.extend((f, "css", r) for f in sos_css for r in weighted_tangents)
    require(len(blocks) == len(cert["sos_ext"]), "weighted block count mismatch")
    for (family, kind, r), factors in zip(blocks, cert["sos_ext"]):
        if factors:
            add_block(family, kind, factors, weighted=True, tangent=r)
    return tables, normalizer, Fraction(loss, integer(cert["q_denom"]))


def permutation_words():
    """Return the exact orbit with multiplicities, sharing the action on five-edge chunks."""
    orders = list(itertools.permutations(range(6)))
    pairs = list(itertools.combinations(range(6), 2))
    digits = [[[], [], []] for _ in pairs]
    for order in orders:
        inverse = {vertex: i for i, vertex in enumerate(order)}
        for edge, (a, b) in enumerate(pairs):
            i, j = inverse[a], inverse[b]
            shift = pair_shift(min(i, j), max(i, j))
            digits[edge][1].append((1 if i < j else 2) << shift)
            digits[edge][2].append((2 if i < j else 1) << shift)

    @lru_cache(maxsize=3 * 243)
    def chunk(start, code):
        words = [0] * len(orders)
        for edge in range(start, start + 5):
            code, trit = divmod(code, 4)
            require(trit < 3, "invalid edge in representative")
            if trit:
                words = [a | b for a, b in zip(words, digits[edge][trit])]
        return words

    def orbit(code):
        require(0 <= code < 1 << 30, "invalid six-vertex code")
        parts = (chunk(0, code & 1023), chunk(5, (code >> 10) & 1023), chunk(10, code >> 20))
        return Counter(a | b | c for a, b, c in zip(*parts))

    return orbit


@dataclass
class AffineRows:
    denominator: int
    loss: Fraction
    rows: list

    def maximum(self, endpoint):
        numerator = max(endpoint.denominator*u + endpoint.numerator*v for u, v in self.rows)
        return Fraction(numerator, self.denominator * endpoint.denominator)

    def lower_boundary(self):
        # At the known strictly negative upper endpoint, only negative slopes
        # constrain how far left the interval can extend.
        return max(((Fraction(-u, v), i) for i, (u, v) in enumerate(self.rows) if v < 0),
                   default=(Fraction(0), None))


def affine_rows(certificates, models, metadata):
    """Compute all model intercepts/slopes once. Each signed lane is one certificate."""
    require(bool(certificates) and len(models) == 6583, "expected certificates and all six-vertex models")
    compiled = [make_terms(cert, metadata) for cert in certificates]
    results = [AffineRows(720 * normalizer, loss, []) for _, normalizer, loss in compiled]

    # Even after summing 720 orderings, the absolute value in every lane is
    # below half the radix. Signed packing is linear, including negative inputs.
    bound = 0
    for tables, _, _ in compiled:
        word_bound = 0
        for (kind, _, _), table in tables.items():
            if kind == "css":
                magnitudes = (abs(a) + abs(b) + abs(c) for a, b, c in table.values())
            else:
                magnitudes = map(abs, table.values())
            word_bound += max(magnitudes, default=0)
        bound = max(bound, word_bound)
    bits = (720 * bound).bit_length() + 1
    radix = 1 << bits
    combined = {}
    for lane, (tables, _, _) in enumerate(compiled):
        shift = bits * lane
        for layout, table in tables.items():
            out = combined.setdefault(layout, {})
            if layout[0] == "css":
                for key, (chi, src, const) in table.items():
                    x, y, z = out.get(key, (0, 0, 0))
                    out[key] = (x + (chi << shift), y + (src << shift), z + (const << shift))
            else:
                for key, value in table.items():
                    out[key] = out.get(key, 0) + (value << shift)
    del compiled
    degree = combined["degree", 0, (1 << 20) - 1]
    base = [(mask, q) for (kind, _, mask), q in combined.items() if kind == "base"]
    ind = [(k, mask, q) for (kind, k, mask), q in combined.items() if kind == "ind"]
    css = [(k, mask, q) for (kind, k, mask), q in combined.items() if kind == "css"]
    all_in, source = [], []
    for row in range(1 << 10):
        digits = [(row >> (2*i)) & 3 for i in range(5)]
        all_in.append([all(d == 1 for d in digits[:k]) for k in range(6)])
        source.append([2 not in digits[:k] and not all_in[row][k] for k in range(6)])

    def take_lane(packed):
        rest, value = divmod(packed, radix)
        if value >= radix // 2:
            return rest + 1, value - radix
        return rest, value

    orbit = permutation_words()
    distinct = 0
    for code in models:
        words = orbit(code)
        distinct += len(words)
        total_u = total_v = 0
        for word, count in words.items():
            row5, row4 = word >> 20, (word >> 12) & 255
            lam = degree.get(word & ((1 << 20) - 1), 0)
            u = lam if row5 & 3 == 1 else 0
            v = -lam
            for mask, q in base:
                u += q.get(word & mask, 0)
            for k, mask, q in ind:
                weight = q.get(word & mask, 0)
                if source[row5][k]:
                    u += weight
                if not all_in[row5][k]:
                    v -= weight
            for k, mask, q in css:
                value = q.get(word & mask)
                if value:
                    chi, src, const = value
                    if all_in[row4][k] and all_in[row5][k] and row5 >> 8 == 0:
                        u += chi
                    if source[row4][k]:
                        u += src
                    u += const
                    v -= src
            total_u += count * u
            total_v += count * v
        for result in results:
            total_u, u = take_lane(total_u)
            total_v, v = take_lane(total_v)
            result.rows.append((u, v))
        require(total_u == total_v == 0, "signed coefficient lane overflow")
    return results, distinct


def verify_rows(cert, scores):
    lo = Fraction(integer(cert["c_low_num"]), integer(cert["c_low_den"]))
    hi = Fraction(integer(cert["c_high_num"]), integer(cert["c_high_den"]))
    require(0 < lo < hi <= 1 and cert["m"] == 6 and cert["num_models"] == len(scores.rows),
            "incorrect interval or model count")
    maxima = []
    for endpoint, field in ((lo, "max_S_low"), (hi, "max_S_high")):
        actual = scores.maximum(endpoint)
        require(actual < 0, f"nonnegative model at {endpoint}: {actual}")
        require(actual == Fraction(*map(integer, cert[field])), f"incorrect recorded maximum at {endpoint}")
        maxima.append(actual)
        print(f"  {endpoint}: max = {actual}")
    slope = Fraction(max(abs(v) for _, v in scores.rows), scores.denominator)
    epsilon = -max(maxima) / (2 * (scores.loss + slope + 1))
    frontier, index = scores.lower_boundary()
    print(f"  M = {scores.loss}; B = {slope}; epsilon = {epsilon}")
    print(f"  lower boundary = {frontier}; active representative (zero-based) = {index}")
    return max(Fraction(0), frontier)


def evaluate(cert, models, metadata):
    results, _ = affine_rows([cert], models, metadata)
    verify_rows(cert, results[0])


def extend_upper_bound(anchor, intervals):
    """Chain overlapping checked intervals, including a zero at a sharp lower endpoint."""
    bound = anchor
    for high, low in sorted(intervals, reverse=True):
        require(high >= bound or low >= bound, f"interval gap between {high} and {bound}")
        if high >= bound:
            bound = min(low, bound)
    return bound


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witnesses", type=Path)
    parser.add_argument("flags", type=Path)
    parser.add_argument("extensions", type=Path)
    parser.add_argument("certificates", type=Path, nargs="+")
    parser.add_argument("--anchor", type=Fraction, help="established upper bound for interval chaining")
    args = parser.parse_args()
    models = checked_models(args.witnesses)
    metadata = flag_ids(args.flags, args.extensions)
    certificates = [json.loads(path.read_bytes()) for path in args.certificates]
    results, distinct = affine_rows(certificates, models, metadata)
    print(f"{len(models)} models, {distinct} distinct labelings, {len(models)*720} weighted orderings")
    intervals = []
    for path, cert, scores in zip(args.certificates, certificates, results):
        print(f"Direct six-vertex evaluation: {path.name}", flush=True)
        lower = verify_rows(cert, scores)
        intervals.append((Fraction(integer(cert["c_high_num"]), integer(cert["c_high_den"])), lower))
    if args.anchor is not None:
        bound = extend_upper_bound(args.anchor, intervals)
        print(f"Chained cStar upper bound from {args.anchor}: {bound} ({float(bound):.12f})")


if __name__ == "__main__":
    main()

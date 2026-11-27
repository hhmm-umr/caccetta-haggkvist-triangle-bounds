#!/usr/bin/env python3
"""Count canonical five- and six-vertex models containing the four critical-arc patterns."""

import itertools
import json
from pathlib import Path

from exact_certificate import require
from verify_six_vertex import decode, file_code


def has_arcs(graph, *pairs):
    return all(graph[u][v] == 1 for u, v in pairs)


def pattern1(g, v, w, x, y, z):
    return (v != y and w != z and y != z and
            has_arcs(g, (v, w), (v, x), (v, z), (w, x), (w, y), (y, x), (x, z)) and
            g[v][y] == 0 and g[w][z] == 0)


def pattern2(g, u, v, w, x, z):
    return (u != x and v != z and w != x and x != z and
            has_arcs(g, (u, v), (u, w), (u, z), (v, w), (v, x), (w, z)) and
            g[u][x] == 0 and g[v][z] == 0 and g[w][x] == 0)


def pattern3(g, u, v, vp, w, x):
    return (v != vp and u != w and x != w and
            has_arcs(g, (u, v), (u, vp), (u, x), (v, w), (vp, w), (vp, x)) and
            g[u][w] == 0 and g[x][w] == 0 and g[v][x] != 1)


def pattern4(g, u, v, w, x, y):
    return (u != w and v != x and v != y and
            has_arcs(g, (u, v), (v, w), (w, x), (u, x), (x, y)) and
            g[u][w] == 0 and g[v][x] == 0 and
            not (g[v][y] == 1 and g[w][y] == 1) and not (g[u][y] == 1 and g[w][y] == 1))


def main():
    data = Path(__file__).resolve().parents[1] / "certs" / "canon_witnesses_m6.json"
    models = json.loads(data.read_bytes())["models"]
    patterns = (pattern1, pattern2, pattern3, pattern4)
    # The Lean predicates quantify over all five-tuples, including repetitions.
    tuples = list(itertools.product(range(5), repeat=5))
    orders = list(itertools.permutations(range(5)))
    labels = {}
    hits = [0] * len(patterns)
    free = 0
    for code in models["5"]:
        g = decode(5, code)
        present = [any(pattern(g, *t) for t in tuples) for pattern in patterns]
        for i, found in enumerate(present):
            hits[i] += found
        contains_pattern = any(present)
        free += not contains_pattern
        for word in {file_code(g, order) for order in orders}:
            require(word not in labels, "duplicate five-vertex isomorphism class")
            labels[word] = contains_pattern
    print(f"Five vertices: individual counts {hits}, union {len(models['5']) - free}, "
          f"pattern-free {free}/{len(models['5'])}")

    # Every witness lies in some five-element subset of a six-vertex host.
    subsets = list(itertools.combinations(range(6), 5))
    free = 0
    for code in models["6"]:
        g = decode(6, code)
        free += not any(labels[file_code(g, s)] for s in subsets)
    print(f"Six vertices: union {len(models['6']) - free}, pattern-free {free}/{len(models['6'])}")


if __name__ == "__main__":
    main()

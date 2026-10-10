#!/usr/bin/env python3
"""Exact finite exhaustive audit for Erdős 128 / JSP-000134.

No dependencies. Checks original half-set local density using integer
arithmetic rather than a surrogate average-density condition.
Only n <= 6 is exhaustive; this is NOT a proof for unbounded orders.
"""
from itertools import combinations

def analyse(n: int):
    if not 0 <= n <= 6:
        raise ValueError("Only n <= 6 is exhaustively certified")
    edges = tuple(combinations(range(n), 2))
    triangles = tuple(combinations(range(n), 3))
    size = n // 2  # 2|S| + 1 >= n
    critical = tuple(combinations(range(n), size))
    edge_index = {pair: i for i, pair in enumerate(edges)}
    triangle_masks = tuple(sum(1 << edge_index[e] for e in combinations(t, 2))
                           for t in triangles)
    critical_masks = tuple(sum(1 << edge_index[e] for e in combinations(s, 2))
                           for s in critical)
    triangle_free = density_yes = both = 0
    witness = None
    for g in range(1 << len(edges)):
        no_triangle = all(g & t != t for t in triangle_masks)
        # Strict integer inequality 50*e(S) > n*n.
        # Only minimum-size S must be tested: adding vertices cannot
        # remove induced edges.
        local = all(50 * (g & s).bit_count() > n*n for s in critical_masks)
        triangle_free += no_triangle
        density_yes += local
        if no_triangle and local:
            both += 1
            witness = g
    return {
        "n": n, "edges_possible": len(edges), "graphs": 1 << len(edges),
        "half_size": size, "triangle_free": triangle_free,
        "local_density_satisfied": density_yes,
        "triangle_free_and_local_density": both, "counterexample": witness,
    }

def main():
    for n in range(3, 7):
        row = analyse(n)
        print(row)
        if row["triangle_free_and_local_density"]:
            raise SystemExit("Counterexample found")
    n = 5
    cycle_edges = {tuple(sorted((i, (i+1) % n))) for i in range(n)}
    bad_pairs = [pair for pair in combinations(range(n), 2) if pair not in cycle_edges]
    assert len(bad_pairs) == 5
    print("C5 rounding regression: five independent pairs violate the premise.")
    print("PASS: no counterexamples on 3..6 labelled vertices.")

if __name__ == "__main__":
    main()

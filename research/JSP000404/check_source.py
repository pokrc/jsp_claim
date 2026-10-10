#!/usr/bin/env python3
"""Independent exact-arithmetic check of the Erdős #504 web-page formula.

NOT a proof of Sendov's classification. No floating point arithmetic.
The two consecutive N values straddle the printed dyadic-band boundary.
See https://www.erdosproblems.com/504 and Sendov (1995), Thm 4.1.
"""
from fractions import Fraction

def check(m: int) -> tuple[int, int, Fraction, Fraction, Fraction]:
    if m < 3:
        raise ValueError("m must be >= 3")
    n_lower = 2 ** (m - 1) + 2 ** (m - 3)
    n_upper = n_lower + 1
    assert 2 ** (m - 1) < n_lower < n_upper <= 2 ** m
    posted_lower = Fraction(2 * m - 2, 2 * m - 1)  # 1 - 1/(2m-1)
    corrected_lower = Fraction(2 * m - 1, 2 * m + 1)  # 1 - 2/(2m+1)
    upper = Fraction(m - 1, m)  # 1 - 1/m
    assert posted_lower > upper, (m, posted_lower, upper)
    assert corrected_lower < upper, (m, corrected_lower, upper)
    return n_lower, n_upper, posted_lower, corrected_lower, upper

def main() -> None:
    for m in range(3, 64):
        check(m)
    assert check(3) == (5, 6, Fraction(4, 5),
                        Fraction(3, 5), Fraction(2, 3))
    print("PASS 61 dyadic transitions m=3..63; each website lower branch")
    print("decreases at the next point count; numerator-two branch does not.")
    print("m=3: N=5 -> N=6, posted 4*pi/5 > 2*pi/3,")
    print("corrected 3*pi/5 < 2*pi/3.")
    print("STATUS: numerical source-consistency check, NOT full proof.")

if __name__ == "__main__":
    main()

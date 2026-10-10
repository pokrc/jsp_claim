# JSP-000404 / Erdős #504: genuine-angle Lean foundations and source audit

**Status: independent research, NOT a complete proof of the original theorem, NOT an award claim.**

The original problem asks for the sharp angle α_N guaranteed among any N distinct
planar points, for every N >= 3:
https://www.erdosproblems.com/504

## Essential source correction (earlier known)

The current secondary problem page gives, with n >= 3,

- Lower N band: 2^(n-1) < N <= 2^(n-1)+2^(n-3);
  it prints α_N = π(1 - 1/(2n-1)).
- Upper N band: 2^(n-1)+2^(n-3) < N <= 2^n;
  it prints α_N = π(1 - 1/n).

These claims imply α_5 = 4π/5 > α_6 = 2π/3, which is impossible:
guaranteed angles can never decrease when an extra point is added.

**Important attribution:** This is *not* a novel observation of ours.
Jackie1021/jsp000404-lean previously identified and documented the
numerator error, citing B. Sendov, "Minimax of the angles in a plane
configuration of points", Acta Mathematica Hungarica 69 (1995),
pp. 27-46, printed p. 42, Theorem 4.1:
https://github.com/Jackie1021/jsp000404-lean

The primary-source theorem, in Sendov's parameter m >= 2, reads

  α_N = π(1 - 2/(2m+1))
  for 2^m < N <= 2^m + 2^(m-2),

and the second band uses α_N = π(1 - 1/(m+1)).
The secondary site's parameter n equals m+1. Thus, **in the site's
indexing**, the corrected lower formula is π(1 - 2/(2n-1)),
NOT π(1 - 1/(2n-1)) and NOT π(1 - 2/(2n+1)).

This yields α_5 = 3π/5 < α_6 = 2π/3, compatible with monotonicity.
The source's genuine full theorem is not proved by this repository.

## What our Lean development really proves

File: research/JSP000404/SourceAudit.lean.

1. Defines GuaranteedAngle N θ by quantifying over **all finite planar
   configurations** of exactly N points and using Mathlib's actual
   EuclideanGeometry.angle, with three pairwise distinct vertices.
   It does NOT define α_N by the answer formula.
2. Proves guaranteed_mono: any guaranteed angle for n points remains
   guaranteed for m points whenever n <= m.
3. Proves elementary_lower_bound: every N >= 3 point set has a genuine
   angle >= π/3, using Mathlib's triangle-angle-sum theorem.
4. Proves five_in_reported_lower_band / six_in_reported_upper_band and
   printed_values_descend: 4π/5 > 2π/3 is a precise contradiction
   in the source's printed pair of expressions.
5. Proves website_bands_cannot_both_hold, using guaranteed_mono:
   a five-point guarantee of 4π/5 conflicts with a six-point ceiling
   of 2π/3.
6. Proves corrected_values_increase, an arithmetic consistency check
   at the same boundary.

The exact-rational Python checker checks 61 band transitions, n=3..63,
without floating point; it is a regression, not a mathematical proof of
the complete classification.

No custom mathematical axioms, sorry, admit, or native_decide.
The Lean file ends with #print axioms for important theorem targets.
These checks do **not** constitute a proof of the original all-N
minimax classification.

## Reproduce the actual verification

Clone https://github.com/pokrc/jsp_claim, check out branch
research/jsp000404-sendov-audit, then execute:

    lake exe cache get
    lake env lean research/JSP000404/SourceAudit.lean
    python3 research/JSP000404/check_source.py

The GitHub workflow jsp000404-source-audit.yml runs Lean and Python.
Examine the exact commit's real Actions logs before asserting
successful kernel checking; standard package CI builds alone do
not check this research file.

## What's missing for the Justin Sun Prize

Theorem 4.1 includes infinitely many N; its full Lean formalization
would need (i) arbitrary-N threshold lower bounds, (ii) matching upper
configurations, (iii) endpoint and base cases, (iv) correspondence of
the exact corrected 1995 theorem to genuine Euclidean geometry, and
(v) reproducible Lean kernel replay and independent proof authorship
and publication priority review. None of these full claims is asserted
here. Specifically, general lower-bound obligations remain open in
the separate Jackie1021 work as of its 2026-10-04 research checkpoint.

The official rules explicitly exclude weaker theorems, finite cases,
proofs using assumptions as stand-ins, and altered statements:
https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md
https://github.com/TheJustinSunPrize/awards/blob/main/docs/verification.md
https://github.com/TheJustinSunPrize/awards/blob/main/docs/award-process.md

No award PR or claim should be opened based solely on this audit.

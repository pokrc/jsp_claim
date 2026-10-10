# JSP-000404 / Erdős #504 — mandatory award-readiness gate

This is an honest gate audit as of 2026-10-10. **Current decision: NOT ELIGIBLE.**
Our research PR is NOT to be forwarded to the awards repository as a full proof.

## I. Mathematical target (must all be proved)

Define alpha(N) by the supremum of actual planar angles guaranteed
among N distinct points. Do not define alpha(N) by the answer formula.

Use Sendov 1995 Theorem 4.1, parameter m >= 2:

- For 2^m < N <= 2^m + 2^(m-2):
  alpha(N) = pi * (1 - 2 / (2*m + 1)).
- For 2^m + 2^(m-2) < N <= 2^(m+1):
  alpha(N) = pi * (1 - 1 / (m+1)).
- Base cases N=3: pi/3, N=4: pi/2.

**Required universally quantified lower-bound theorems, not finite tests:**

- Every (2^m+1)-point set has an angle >= pi*(1 - 2/(2*m+1))
  for every m >= 2.
- Every (2^m+2^(m-2)+1)-point set has an angle
  >= pi*(1 - 1/(m+1)) for every m >= 2.
- Monotonicity extends thresholds over their bands.
- Independent matching configuration constructions give all upper bounds.
- Every theorem uses genuine Euclidean angles, full distinctness,
  full point-set cardinality, with no extra convexity or generic-position
  hypotheses unless these assumptions are eliminated.

## II. Existing public research and obstacles

The mathematical result belongs to Sendov and prior authors, not to
a newly formalizing submitter.

Relevant prior Lean work:
- https://github.com/TheJustinSunPrize/awards/pull/42
  (numerator discrepancy, geometry definitions, constructions).
- https://github.com/TheJustinSunPrize/awards/pull/100
  (N=5..10 and dyadic cases).
- https://github.com/TheJustinSunPrize/awards/pull/300
  (N=3..8, dyadic thresholds, upper families; a purported general
  capacity-maximum argument is reported to have counterexamples).
- https://github.com/TheJustinSunPrize/awards/pull/647
  (reported complete eleven-point threshold; N=11..16).
- https://github.com/Jackie1021/jsp000404-lean
  (four-/five-center capacity research, still explicitly incomplete).
- https://github.com/Yi-111-a/jsp-000404-blumenthal-sendov
  (a code path sets alpha equal to a piecewise formula by definition,
   not by minimax geometry).

As of this audit we have NOT independently reproduced all those
competitors' proof cones. There is no credible evidence that **our**
code supplies the two full general lower-bound families. A published
paper and a purportedly proved general step still need mathematical
review, especially in light of the public reports of a capacity-lemma
gap. Prior proposals and earliest PUBLIC COMPLETE-proof priority must
be rechecked before any reward submission.

## III. Mechanical formal verification gate

Use the EXACT selected original proof repository and full 40-character
commit hash (not an editable branch reference as sole evidence).

- Pin lean-toolchain, Mathlib revision and transitive dependencies.
- Build cleanly in an isolated environment (cache is not proof of success).
- Kernel-check all original target theorems, and print the fully expanded
  definitions and transitive axioms.
- No sorry/admit, no added mathematical axiom, no native_decide in the
  theorem's dependency cone, no opaque/untrusted escape hatch.
- Theorem statement must be equivalent to the original, corrected
  all-N mathematical classification, not a bounded test, weakened
  quantification or formula-defined alpha.
- Independently check the original mathematics, counterexamples,
  construction endpoints, priority sources, and full Lean replay.
- Publish a check log and a public commit, with source and toolchain
  evidence. Any change to the selected proof commit requires a new audit.

The Justin Sun Prize's lean-verify skill is optional but recommended:
https://github.com/TheJustinSunPrize/awards/blob/main/skills/lean-verify/SKILL.md
https://github.com/TheJustinSunPrize/awards/blob/main/docs/verification.md

## IV. Submission / prize process after (and ONLY after) complete proof

1. Submit source in an original personal or verifiably controlled
   organization repository. Do not copy another team's source.
2. Fork TheJustinSunPrize/awards. Update the appropriate catalog entry
   and index metadata, not Lean source blobs. Open an English PR with
   complete solution publication evidence, exact theorem location,
   full selected commit SHA, reproducible checks, authorship and
   earlier-public work disclosures. Maintainers review mathematically
   before accepting the Lean proof.
3. Have the contribution PR merged. A proof repository alone and an
   open PR are not enough for an accepted claim.
4. Open your own claim-award issue after merge. A pending early claim
   does not meet the merged-PR requirement.
5. Send independent identity verification privately via the organizer's
   official published email. Do not publish ID/payment details on GitHub.
6. The **14-day public-review clock** starts from official candidate
   publication in candidates/, not submission time or PR merge time.
7. Only after review, checks, written recipient confirmation and
   announcement may an award follow. Submission or verification
   alone NEVER establishes entitlement.

Sources:
- https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md
- https://github.com/TheJustinSunPrize/awards/blob/main/docs/award-process.md
- https://github.com/TheJustinSunPrize/awards/blob/main/docs/verification.md

## V. Status of this PR / honest decision

Our present original contribution consists of: universal monotonicity
of angle guarantees, a universal pi/3 lower bound, the true supremum
alpha(N) definition and its monotonicity, an exact certificate exposing
the secondary source's erroneous formula, and exact rational boundary
checks. The numerator error was previously documented elsewhere.

These are useful, independently checkable foundational/correction
results. They DO NOT fill the unrestricted lower-bound proof gap;
therefore the full formalization gate is **FAIL / INCOMPLETE**, whatever
the local CI status may be. No award PR and no claim has been created.

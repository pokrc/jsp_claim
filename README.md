# jsp_claim — Lean 4 research and formalization

[![Lean CI](https://github.com/pokrc/jsp_claim/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/pokrc/jsp_claim/actions/workflows/lean_action_ci.yml)

This is an independently maintained Lean 4 + Mathlib repository for the [Justin Sun Prize problem bank](https://github.com/TheJustinSunPrize/awards). It contains formally checked **statements of specific scope**. A proof of a special case, a finite witness, or a corrected catalog statement is **not** automatically a proof of the complete original Erdős problem or an eligible prize submission.

GitHub account: [pokrc](https://github.com/pokrc). See also [the POKRC repository directory](https://github.com/pokrc/POKRION-Speed-Drone/blob/main/PROJECTS.md).

## Reproduce

Pinned toolchain: `leanprover/lean4:v4.34.0`; Mathlib `v4.34.0`.

```bash
git clone https://github.com/pokrc/jsp_claim.git
cd jsp_claim
lake exe cache get
lake build JspClaim
```

The Lean kernel establishes the actual types of compiled theorems, **not** whether a theorem matches the original published mathematical question. Review the precise statement and its mathematical provenance before reusing or citing it. Use `#print axioms Module.theorem` for a named theorem audit. A green workflow alone is not prize verification.

## Modules in `main`

The following files **exist on the default branch** as of 2026-10-10. The last column is a scope note, not an award determination.

| Lean module | Problem | Verified theorem scope / important limitation |
| --- | --- | --- |
| [JSP000301](JspClaim/JSP000301.lean) | #301 | Explicit Golomb counterexample: the consecutive powerful numbers 12167 and 12168 are not squares; [official PR #1960](https://github.com/TheJustinSunPrize/awards/pull/1960) remains open |
| [JSP000689](JspClaim/JSP000689.lean) ([helpers](JspClaim/JSP000689_helpers.lean)) | #689 | Erdős–Lovász hypergraph degree statement under the file's hypotheses and Fano-plane example; [official PR #2054](https://github.com/TheJustinSunPrize/awards/pull/2054) remains open |
| [JSP000307](JspClaim/JSP000307.lean) | #307 | Single explicit witness (152, 153, 154); source Erdős #372 asks for infinitely many |
| [JSP000598](JspClaim/JSP000598.lean) | #598 | Single pair (87, 88); source Erdős #730 asks for infinitely many |
| [JSP000243](JspClaim/JSP000243.lean) | #243 | Minimum interval span 4 for a finite base case; cited Croot source concerns asymptotic width |
| [JSP000546](JspClaim/JSP000546.lean) | #546 | Example for k=3; source Erdős #672 requires k≥4 |
| [JSP000554](JspClaim/JSP000554.lean) | #554 | Explicit pair (7,11), rather than the source's almost-all-n theorem |
| [JSP000876](JspClaim/JSP000876.lean) | #876 | Constructed intervals may be non-adjacent; the source asks for contiguous intervals |
| [JSP000947](JspClaim/JSP000947.lean) | #947 | Explicit n=45 case; original Erdős #1142 asks for n>105 or infinitely many |

**Do not treat these scope-mismatched cases as complete proofs of the original problem.** Do not assert eligibility, priority or award acceptance from this table. The PR references above identify publicly submitted work, not merged/accepted contributions.

## Research branches (not merged into `main`)

| Branch | Topic | Status |
| --- | --- | --- |
| [research/jsp-000086-erdos68-20261010](https://github.com/pokrc/jsp_claim/tree/research/jsp-000086-erdos68-20261010) | Erdős #68 reciprocal-factorial series; exact statement and auxiliary lemmas | **Unsolved original conjecture; research only** |
| [research/jsp-000134-erdos-128](https://github.com/pokrc/jsp_claim/tree/research/jsp-000134-erdos-128) | Six-vertex problem audit | [Draft PR #1](https://github.com/pokrc/jsp_claim/pull/1), research only |
| [research/jsp000404-sendov-audit](https://github.com/pokrc/jsp_claim/tree/research/jsp000404-sendov-audit) | Sendov / Erdős 504 audit | [Draft PR #2](https://github.com/pokrc/jsp_claim/pull/2), research only |

These branches are isolated to prevent incomplete proof investigations from being mistaken for formal competition submissions.

## Historical attempts and corrections

Early commits additionally contained JSP000183, JSP000625 and JSP000558. Those files are **absent from the current default branch**. JSP000183 and JSP000625 tracked external formalizations too closely to justify an independent submission; JSP000558 was a partial k=2 case. Relevant third-party credit must always be preserved.

JSP000876 and JSP000947 were previously described as "removed," **but both are currently present on `main`**; this README corrects that mismatch and labels their proof scopes instead. JSP000554 previously appeared twice in the module list; only one module exists.

The catalog-description corrections referred to in the older history are #3263 (#876), #3264 (#947), and #3342 (#554) in [the official awards repository](https://github.com/TheJustinSunPrize/awards). These references do not imply they were accepted.

## Submission policy

Read [official contribution requirements](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md) and the [award process](https://github.com/TheJustinSunPrize/awards/blob/main/docs/award-process.md). A qualifying Lean submission requires the *complete original problem* to have a reviewed mathematical solution and a matching reproducible Lean proof; it also requires attribution, a pinned original proof commit and maintainer review. Do not file claims for isolated finite witnesses or unproved conjectures.

## License

See [LICENSE](LICENSE) for this repository. Other cited authors and upstream formalizations retain their own attribution and licensing.

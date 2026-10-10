# Justin Sun Prize readiness audit — 2026-10-10

**Result:** Not currently eligible to receive an award. This report distinguishes mathematical validity, Lean kernel checking, official project acceptance, and competition priority. It is not an award claim.

## Live official records checked on 2026-10-10

| JSP | Mathematical result | Lean proof source | Official PR | Claim issue | Award status |
| --- | --- | --- | --- | --- | --- |
| [000301](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301) | Solomon W. Golomb's 1970 counterexample; `Solved` in catalog | [original pinned proof](https://github.com/pokrc/jsp_claim/blob/0a2313e9c66df33d010ffeea30f12172ded89c0d/JspClaim/JSP000301.lean) | [#1960](https://github.com/TheJustinSunPrize/awards/pull/1960), open, not merged | [#1961](https://github.com/TheJustinSunPrize/awards/issues/1961), early/unaccepted | **Not eligible**; catalog `Lean proof: No`, `Eligible: No` |
| [000689](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000689) | Erdős–Lovász 1975; `Solved` in catalog | [original pinned proof](https://github.com/pokrc/jsp_claim/blob/728e28c4233d37f7d319b8a7b824d79b3976d552/JspClaim/JSP000689.lean) | [#2054](https://github.com/TheJustinSunPrize/awards/pull/2054), open, not merged | [#2055](https://github.com/TheJustinSunPrize/awards/issues/2055), early/unaccepted | **Not eligible**; catalog `Lean proof: No`, `Eligible: No` |
| [000086](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000086) | Open irrationality problem | [research branch](https://github.com/pokrc/jsp_claim/tree/research/jsp-000086-erdos68-20261010), only auxiliary facts | No qualifying submission | No qualifying claim | **Not eligible**; the main mathematical theorem is unproved |

The claim issues are already opened; do not create duplicates. A claim issue alone is not an accepted award application.

## Exact-statement improvements in this branch

1. `JspClaim/JSP000301_StatementBridge.lean` explicitly quantifies over **positive** consecutive integers and proves the negation of the original yes/no universal claim using the independently checked Golomb witness. Existing prize PR commit remains the historical selected source; this newer bridge does not retroactively improve priority.
2. `JspClaim/JSP000689_Exponential.lean` derives a **literal exponential base** `(9/8)^r` for `r ≥ 8` from the existing finite Erdős–Lovász bound. The conclusion is explicit, rather than relying solely on informal asymptotic wording. The theorem is still for **finite** hypergraphs and does not establish independent award priority.
3. `ProofAudit.lean` prints the axioms for the original and new target theorems. `lake build JspClaim` and `lake env lean ProofAudit.lean` must be checked on the branch's exact SHA before merging.

## Priority barriers (not repairable by editing README / timestamps)

- **JSP-000301:** Several earlier submitted independent Lean proofs exist, including #2110. See the explicit disclosure on [PR #1960](https://github.com/TheJustinSunPrize/awards/pull/1960). The repository owner **does not** assert priority.
- **JSP-000689:** Earlier published `plby/lean-proofs/src/latest/ErdosProblems/Erdos833.lean` predates our selected proof; see the explicit disclosure on [PR #2054](https://github.com/TheJustinSunPrize/awards/pull/2054). The repository owner **does not** assert priority.

Both official PRs had zero maintainer review submissions or inline comments at the time of this audit. Their GitHub `mergeable_state` was `blocked`; a successful local build cannot clear official maintainer-approval requirements.

## Official award gate

Per [official participation and claim procedure](https://github.com/TheJustinSunPrize/awards/blob/main/docs/award-process.md) and [contribution requirements](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md):

1. The mathematical solution to the **complete original problem** must pass review. Finite examples for an infinitude conjecture and weaker results do not count.
2. The matching original Lean proof must be independently verified at a pinned, original 40-character commit; authorship/attribution and proof/statement scope must be checked.
3. The participant's official catalog PR must be reviewed and merged for the Lean role. Official catalog eligibility follows the maintainers' accepted record, not self-assessment.
4. Public candidate registration triggers a separate **14-day public review**; identity verification by the official email address and written recipient confirmation follow. A PR merge by itself is not an award.
5. The earliest **verified** qualifying public proof source takes priority; an earlier Git timestamp by itself is not conclusive authorship or priority evidence.

**Never** backdate, force-push, modify the original historical selected commit or claim another contributor's solution. Do not submit research-only branches as prize proofs.

## Next decision

- Preserve and make available the pinned evidence for #301/#689; respond if official reviewers request corrections. Do not spam duplicate claims.
- For a realistic new award attempt, choose a catalog `Solved` problem with `Lean proof: No`, verify the complete mathematics, search for **existing complete proofs outside the prize repository**, and only then author an **independent** complete Lean formalization. No award can be promised.

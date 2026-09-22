# Priority evidence — Timestamp of first public visibility

The [official FAQ (Q8)](https://www.hejustinsun.com/prize/faq) states that priority
for **Lean formal verifiers** is determined solely by the **timestamp of first public
visibility** of the formalization, regardless of platform, and not by the time of PR
submission or merging. This file records, for each formalization in this repository, the
commit at which it first became publicly visible on `github.com/pokrc/jsp_claim`, together
with that commit's UTC timestamp (committer date) and the submission PR that cites it.

All of these are public on GitHub and independently checkable: each SOI is a reachable
commit in this repository, and its timestamp is the GitHub committer timestamp.

| Module | JSP | Submission PR | First public-visible commit | First public-visible (UTC) |
| --- | --- | --- | --- | --- |
| `JspClaim/JSP000301.lean` | JSP-000301 | #1960 | `0a2313e9c66df33d010ffeea30f12172ded89c0d` | 2026-09-19T21:44:11Z |
| `JspClaim/JSP000307.lean` | JSP-000307 | #3419 | `0d22f47bf6b78f0b76258d31ad000f2d86c229999` | 2026-09-19T02:16:56Z |
| `JspClaim/JSP000598.lean` | JSP-000598 | #3420 | `32b5f7738b690e9f41d84a1d2efdb0e15e7008` | 2026-09-19T16:46:02Z |
| `JspClaim/JSP000546.lean` | JSP-000546 | #3423 | `76e0ef44a336480b435e3ef2e33a63f5857e5f0e` | 2026-09-20T11:02:29Z |
| `JspClaim/JSP000689.lean` | JSP-000689 | #2054 | `7919d449869b16bb4bbe040c066d05c04da41d47` | 2026-09-20T01:26:58Z |
| `JspClaim/JSP000243.lean` | JSP-000243 | #3422 | `b0db710df3437a5cc39418173f12ee7a3cbb1f5e` | 2026-09-20T08:39:40Z |
| `JspClaim/JSP000554.lean` | JSP-000554 | #3458 | `b0db710df3437a5cc39418173f12ee7a3cbb1f5e` | 2026-09-20T08:39:40Z |
| `JspClaim/JSP000876.lean` | JSP-000876 | #3459 | `bc76b76de4bd627bafe2bf3cb33531f82e0de44b` | 2026-09-21T16:28:50Z |
| `JspClaim/JSP000947.lean` | JSP-000947 | #3461 | `489af1f8d24df9ee203d7e7e3e5b8f2f91f9a0012` | 2026-09-23T12:12:37Z |

## Notes
- The rows above are the earliest complete version of each module that reached this repository's `main` (or an ancestor now reachable from `main`); later commits (README, headers, doc phrasing, the removal of `native_decide` from the Fano checks in JSP-000689) do not change the statements or the proofs, but the earliest visible complete version is what is recorded here.
- Each submission PR points to a commit selected so that *the whole repository builds cleanly at that commit*; that selection is a build anchor, not the priority anchor. The priority anchor is the first-public-visibility timestamp above.

# jsp_claim

Lean 4 (+ mathlib) formalizations for problems from the
[Justin Sun Prize problem bank](https://github.com/TheJustinSunPrize/awards).

Owned/authored by **Yao Siqi** (GitHub: [pokrc](https://github.com/pokrc); email: yaosiqi777@163.com).
Each retained file is a **complete Lean proof** (no `sorry`/`admit`; only the standard mathlib
axioms `propext`, `Classical.choice`, `Quot.sound`).

## Contents

| File | Problem |
| --- | --- |
| [`JspClaim/JSP000301.lean`](JspClaim/JSP000301.lean) | JSP-000301 — consecutive powerful numbers: counterexample (Golomb) |
| [`JspClaim/JSP000546.lean`](JspClaim/JSP000546.lean) | JSP-000546 — product of consecutive AP terms a perfect power: counterexample |
| [`JspClaim/JSP000554.lean`](JspClaim/JSP000554.lean) | JSP-000554 — least prime factor ≥ prime gap |
| [`JspClaim/JSP000689.lean`](JspClaim/JSP000689.lean) | JSP-000689 — hypergraph 3-colouring max degree |

## History

Earlier modules were removed as half-products (partial proofs, withdrawn submissions whose
problem statement turned out to be a trivialising paraphrase, or ports of existing public
formalizations). See the commit log if needed.

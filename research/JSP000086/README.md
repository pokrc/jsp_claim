# JSP-000086 — Erdős #68 research dossier (NOT A SOLUTION)

**Status as checked on 2026-10-10:** original conjecture remains open. This is a research branch only, not a Justin Sun Prize submission, solver claim, or Lean-formalizer claim.

## 1. Exact problem

Let
\[
S=\sum_{n=2}^{\infty}\frac{1}{n!-1}.
\]
Does \(S\not\in\mathbb{Q}\)? The n=2 term is **1**. Changing the lower endpoint to 3 is a statement mismatch unless the omitted rational term is carefully accounted for.

Formal target: `Irrational (∑' n : ℕ, (1 : ℝ) / (((n + 2).factorial : ℝ) - 1))`; see `JspClaim/JSP000086.lean`. Its `exact_target` theorem is only a definitional-equivalence check. It is not a proof of irrationality.

## 2. Provable auxiliary steps

* For \(n\ge2\), \(n!\ge2\), so \(n!-1\ge n!/2\) and \(0<1/(n!-1)\le 2/n!\). Hence the series converges absolutely.
* For any real \(x>1\), 
  \[
  \frac1{x-1}=\frac1x+\frac1{x(x-1)}.
  \]
  Therefore \(S=e-2+R\), where \(R=\sum_{n=2}^{\infty}1/[n!(n!-1)]\). The irrationality of \(e\) alone **does not** establish the irrationality of \(S\).
* The geometric expansion \(1/(n!-1)=\sum_{k\ge1}1/(n!)^k\) is already proved upstream in Google DeepMind's formal-conjectures repository. Do not claim authorship of that result.
* The first terms, with the **correct** starting index, are \(1,1/5,1/23,1/119,\ldots\). The first three sum to \(143/115\). This is a finite calculation, not evidence of irrationality.

## 3. Why the basic denominator proof cannot close

Define \(S_N=\sum_{n=2}^{N}1/(n!-1)\), \(T_N=S-S_N>0\), and \(D_N=\prod_{n=2}^{N}(n!-1)\).

Clearly \(D_NS_N\in\mathbb{Z}\). A naive irrationality argument would hope that the positive number \(D_NT_N\) is eventually less than \(1/b\) if \(S=a/b\). This approach *fails*, even before estimating the full tail.

At \(N=5\),
\[
D_5=1\cdot5\cdot23\cdot119=13685>6!=720,
\]
and \(T_5>1/(6!-1)=1/719\). Consequently \(D_5T_5>13685/719>1\).

More strongly, \(D_N>(N+1)!\) for all \(N\ge5\). The base case holds above. If true at \(N\), then
\[
D_{N+1}=D_N((N+1)!-1)>(N+1)!((N+1)!-1)>(N+2)!,
\]
because \((N+1)!-1>N+2\) for \(N\ge5\).
Thus \(D_N T_N> D_N/((N+1)!-1)>1\) for every \(N\ge5\). This strictly rules out the **simple product-denominator small-tail argument**; it does **not** rule out sophisticated integer linear forms or other proofs.

Using the least common multiple rather than the product does not by itself solve this: factors \(n!-1\) may overlap, and there is currently no bound adequate to derive a contradiction.

## 4. Honest boundary of this research

The decisive step \(S\notin\mathbb{Q}\) is **unproved**. No theorem, axiom, `sorry`, `admit`, or unproved auxiliary assumption is used to assert that result. The Lean source intentionally records only the target and several elementary fully justified facts.

This dossier cannot be submitted as a qualifying solution or Lean proof under the official award rules.

## 5. Award submission gate

Before an official PR, require all of the following:

1. A complete mathematical proof (or proof of rationality, should the affirmative conjecture fail) that resolves the exact original infinite series.
2. A corresponding Lean 4 theorem, matching the original statement in both index and type, with no `sorry`, `admit`, or additional unproved axioms. Reproducible clean build plus `#print axioms` audit.
3. Formal proof in a contributor-owned repository with branch and pinned 40-character commit SHA, independently verifiable public history, and mathematical attribution.
4. Official fork catalog PR and maintainer review. A merged PR is needed for a Lean award claim. Later steps include 14-day public review, contributor verification, and written recipient confirmation. A passing build or submitted PR is not an award.

## References

* Original problem and open status: https://www.erdosproblems.com/68
* Official problem record: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000086
* Rules: https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md
* Submission process: https://github.com/TheJustinSunPrize/awards/blob/main/docs/award-process.md
* Upstream formal statement and established geometric-sum lemma: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/68.lean

**Author/account:** `pokrc`. Scope: original research notes, target wrapper, arithmetic checks. Not a claim of an original solution to Erdős #68.

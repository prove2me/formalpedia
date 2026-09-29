-- Prove2me | Theorems.Thm_buchholz_evenq_trace_pairbound
-- name    : buchholz_evenq_trace_pairbound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-23T21:17:56.338937+00:00
-- url     : https://prove2.me/theorems/cedbb298-4548-4338-8abe-3cf4fc8a468b
-- statement:
--   **Buchholz even-moment trace pairbound (the combinatorial core of the noncommutative Khintchine inequality).** Let $S_\varepsilon = p^{-1}\sum_{(i,j)} \varepsilon_{ij}\,\delta_{ij}\,X_{ij}\, e_i e_j^{\top}$ be the symmetrized coordinate Rademacher series (`rademacherSampledMatrix`), where $\delta_{ij}=\mathbf 1[(i,j)\in\Omega]$ and $\varepsilon_{ij}\in\{\pm1\}$ are independent signs.  For every integer $n\ge 1$, the sign-averaged even trace moment is dominated by the pair-partition count times the larger diagonal-Gram trace:
--
--   $$\mathbb{E}_{\varepsilon}\big[\operatorname{tr}\big((S_\varepsilon S_\varepsilon^{\top})^{n}\big)\big]\;\le\;\frac{(2n)!}{2^{n}\,n!}\;\max\Big(\operatorname{tr}\big((\textstyle\sum A A^{\top})^{n}\big),\operatorname{tr}\big((\textstyle\sum A^{\top}A)^{n}\big)\Big).$$
--
--   Here $\sum_{(i,j)} A_{ij}A_{ij}^{\top} = \operatorname{diag}_i(p^{-2}\,\mathrm{rowEnergy}_i)$ and $\sum_{(i,j)} A_{ij}^{\top}A_{ij} = \operatorname{diag}_j(p^{-2}\,\mathrm{colEnergy}_j)$ are diagonal, so their $n$-th-power traces are exactly $\sum_i (p^{-2}\,\mathrm{rowEnergy}_i)^n = (\texttt{sampledRowGramSchatten}\,\Omega\,p\,X\,(2n))^{2n}$ and likewise for columns; the right-hand side is stated in this Schatten form.  The constant $\frac{(2n)!}{2^n n!} = (2n-1)!!$ is the number of perfect matchings (pair-partitions) of a $2n$-element set; combined with $(2n-1)!!\sim\sqrt2\,(2n/e)^n$ it yields Buchholz's optimal $\sqrt{q}$ factor with constant $C_K = 2^{-1/4}\sqrt{\pi/e}$.
--
--   This is the genuinely deep estimate of the moment method: the K-expand bricks (`trace_pow_eq_walk`, `E_sign_monomial`) reduce the left side to a sum over *matched* closed bipartite walks (every coordinate-edge multiplicity even), and this lemma bounds that matched sum by the pair-partition count times the Gram traces.  Source: Buchholz, *Operator Khintchine inequality in non-commutative probability*, Math. Ann. 319 (2001) 1–16, §2–3; CR2009 (arXiv:0805.4471) §6.1 Lemma 6.1.
-- source:
--   Buchholz, Operator Khintchine inequality in non-commutative probability, Math. Ann. 319 (2001) 1-16, sections 2-3 (even-moment combinatorial estimate and optimal constant D_{2n}=((2n)!/(2^n n!))^{1/2n}); CR2009 (arXiv:0805.4471) section 6.1 Lemma 6.1

import Definitions.Def_matrix_completion_gram_schatten
open MatrixCompletion
open scoped BigOperators

theorem buchholz_evenq_trace_pairbound
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          Matrix.trace
            ((rademacherSampledMatrix Omega eps p X *
                (rademacherSampledMatrix Omega eps p X).transpose) ^ n))
      ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
          max ((sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n))
              ((sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)) := by sorry

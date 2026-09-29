-- Prove2me | Theorems.Thm_gram_schatten_le_exp_half_variance_scale
-- name    : gram_schatten_le_exp_half_variance_scale
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-22T02:14:52.143075+00:00
-- url     : https://prove2.me/theorems/be7a47a4-4cd5-421e-94a3-75d7a9ebdb47
-- statement:
--   The $\ell_q\to\ell_\infty$ Gram comparison plus window collapse of Candes-Recht 2009, Section 6.1, p.24 (the displayed bound $\lVert X\rVert\le\lVert X\rVert_{S_q}\le e\lVert X\rVert$ for $q\ge\log n$, and the 'after a little algebra' step). For nonnegative reals, $(\sum_{i\in[N]} a_i^q)^{1/q}\le N^{1/q}\max_i a_i$; applied to the diagonal Gram entries this gives $$\max\big(\mathrm{sampledRowGramSchatten},\ \mathrm{sampledColumnGramSchatten}\big)\ \le\ (\max(n_1,n_2))^{1/q}\cdot \mathrm{rademacherSampledVarianceScale}.$$ In the window $q\ge\beta\log(\max(n_1,n_2))$ with $\beta>2$ the polynomial factor collapses to an absolute constant: $(\max n)^{1/q}\le e^{1/\beta}\le e^{1/2}$. Hence the diagonal-Gram Schatten norms are bounded by $e^{1/2}\cdot\mathrm{rademacherSampledVarianceScale}$. Here $\mathrm{rademacherSampledVarianceScale}=p^{-1}\sqrt{\max(\mathrm{sampledRowEnergyMax},\mathrm{sampledColumnEnergyMax})}$ is the $\ell_\infty$ variance scale. Hypotheses: $0\le p$, $\beta>2$, $1\le q$, $q\ge\beta\log(\max(n_1,n_2))$.
-- source:
--   Candes, Recht, Exact matrix completion via convex optimization, arXiv:0805.4471, Section 6.1, Lemma 6.1, p.24.

import Definitions.Def_matrix_completion_gram_schatten
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MatrixCompletion

theorem gram_schatten_le_exp_half_variance_scale {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : Matrix (Fin n1) (Fin n2) ℝ)
    (q β : Real) (hp : 0 ≤ p) (hβ : 2 < β) (hq : 1 ≤ q)
    (hqlog : q ≥ β * Real.log (↑(max n1 n2))) :
    max (sampledRowGramSchatten Omega p X q) (sampledColumnGramSchatten Omega p X q) ≤
      Real.exp (1 / 2) * rademacherSampledVarianceScale Omega p X := by
  sorry

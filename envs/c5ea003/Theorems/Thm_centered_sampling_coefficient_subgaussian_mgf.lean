-- Prove2me | Theorems.Thm_centered_sampling_coefficient_subgaussian_mgf
-- name    : centered_sampling_coefficient_subgaussian_mgf
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T00:24:21.298615+00:00
-- url     : https://prove2.me/theorems/99db0c4a-9ceb-4586-8e31-391ce10b9582
-- statement:
--   Sub-Gaussian MGF bound for the centered-sampling coefficient statistic on the Bernoulli powerset measure. For $0 < p \le 1$ and any $\lambda$, the moment generating function of $\mathrm{Coeff}(\Omega)=\sum_w p^{-1}(\mathbf 1[w\in\Omega]-p)B_w$ is sub-Gaussian: $\mathbb E[\exp(\lambda\,\mathrm{Coeff})] \le \exp\!\big(\lambda^2\,\lVert B\rVert_F^2/(8p^2)\big)$. This follows by applying the per-coordinate two-point Hoeffding MGF bound to each factor of the exact MGF factorization (each factor being the MGF of a centered two-point increment with range $\lambda p^{-1}B_w$) and multiplying over coordinates.
-- source:
--   Hoeffding 1963; Boucheron, Lugosi, Massart, Concentration Inequalities, OUP 2013, Lemma 2.2 and Ch. 2 (Cramer-Chernoff method); Candes-Recht 2009, arXiv:0805.4471, Section 6.

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.SpecialFunctions.Exp
open MatrixCompletion
open scoped BigOperators Classical

theorem centered_sampling_coefficient_subgaussian_mgf {n₁ n₂ : ℕ}
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) (lam : ℝ) :
    bernoulliExpectation p
        (fun Omega =>
          Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Omega p B))) ≤
      Real.exp (lam ^ 2 * frobeniusNormSq B / (8 * p ^ 2)) := by sorry

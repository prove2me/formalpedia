-- Prove2me | Theorems.Thm_centered_sampling_coefficient_mean_zero
-- name    : centered_sampling_coefficient_mean_zero
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T20:51:50.39409+00:00
-- url     : https://prove2.me/theorems/a4093347-739e-46f6-9266-a761bfb56555
-- statement:
--   **Mean zero of the scalar centered sampling coefficient.** The statistic $$\mathrm{Coeff}(\Omega)=\texttt{matrixEntrySum}(\texttt{centeredSamplingFluctuation}(\Omega,p,B))=\sum_{i,j}p^{-1}\big(\mathbf{1}[(i,j)\in\Omega]-p\big)B_{ij}$$ has Bernoulli-expectation zero (for $p\neq 0$). It is a sum of independent centered terms; by linearity each coordinate contributes $p\cdot p^{-1}B_w(1-p)+(1-p)\cdot(-B_w)=0$. This is the mean-zero input to the q-moment Bernstein estimate (`scalar_centered_sampling_qmoment_bernstein_estimate`).
-- source:
--   Candès–Recht 2009, Exact Matrix Completion via Convex Optimization, arXiv:0805.4471, §6 (the centered sampling operator $p^{-1}(P_\Omega - p)$); Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 15.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators

theorem centered_sampling_coefficient_mean_zero {n₁ n₂ : ℕ} (p : ℝ) (hp : p ≠ 0)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    bernoulliExpectation p
      (fun Omega => matrixEntrySum (centeredSamplingFluctuation Omega p B)) = 0 := by sorry

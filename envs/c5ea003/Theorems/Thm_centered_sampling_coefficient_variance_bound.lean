-- Prove2me | Theorems.Thm_centered_sampling_coefficient_variance_bound
-- name    : centered_sampling_coefficient_variance_bound
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T21:07:33.731246+00:00
-- url     : https://prove2.me/theorems/6f4cb035-8ae6-4f07-8df6-c81e7ed90fd5
-- statement:
--   **Variance bound $\sigma^2 \le \|B\|_F^2/p$** for the scalar centered sampling coefficient. From the exact second-moment identity $\mathbb{E}[\mathrm{Coeff}^2]=\frac{1-p}{p}\|B\|_F^2$ and $1-p\le 1$ (for $p\in(0,1]$) with $\|B\|_F^2\ge 0$: $$\mathbb{E}[\mathrm{Coeff}^2]=\frac{1-p}{p}\|B\|_F^2 \le \frac{\|B\|_F^2}{p}.$$ This is the $\sigma^2$ quantity fed (with $L\le\|B\|_\infty/p$) into the q-moment Bernstein estimate $\big(\mathbb{E}|\mathrm{Coeff}|^q\big)^{1/q}\le\sqrt{2q\sigma^2}+qL$.
-- source:
--   Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 15; Candès–Recht 2009, arXiv:0805.4471, §6 (centered sampling operator p⁻¹(P_Ω − p)).

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators

theorem centered_sampling_coefficient_variance_bound {n₁ n₂ : ℕ} (p : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    bernoulliExpectation p
      (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega p B)) ^ 2) ≤
      frobeniusNormSq B / p := by sorry

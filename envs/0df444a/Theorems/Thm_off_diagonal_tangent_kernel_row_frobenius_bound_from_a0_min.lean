-- Prove2me | Theorems.Thm_off_diagonal_tangent_kernel_row_frobenius_bound_from_a0_min
-- name    : off_diagonal_tangent_kernel_row_frobenius_bound_from_a0_min
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-26T01:54:45.034374+00:00
-- url     : https://prove2.me/theorems/8fe87e74-02e9-4197-96c2-f6ae51e023a4
-- statement:
--   Corrected (min) form of the off-diagonal tangent-kernel row Frobenius estimate for Candes-Recht Lemma 6.6. For the kernel K_{ij}=<P_T(e_{ij}),e_w>, self-adjointness of the orthogonal projector P_T gives sum_{i,j} K_{ij}^2 = ||P_T(e_w)||_F^2 = D = alpha_a+beta_b-alpha_a*beta_b, so the off-diagonal Frobenius norm squared is D - K_ww^2 <= D <= 2*mu0*r/min(n1,n2) under A0. Hence the off-diagonal kernel matrix (zeroed at w) has Frobenius norm <= sqrt(2) * sqrt(mu0 * r / min(n1,n2)). NOTE: the max-version off_diagonal_tangent_kernel_row_frobenius_bound_from_a0 is FALSE for rectangular matrices (disproved); this min-version is the correct geometric estimate.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem off_diagonal_tangent_kernel_row_frobenius_bound_from_a0_min :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → A0 S μ₀ →
        ∀ w : Fin n₁ × Fin n₂,
          frobeniusNorm
              (fun i j =>
                if (i, j) = w then 0
                else tangentCoordinateKernel S i j w.1 w.2) ≤
            Cker * Real.sqrt
              (μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := by sorry

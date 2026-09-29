-- Prove2me | Theorems.Thm_tangent_coordinate_kernel_diagonal_bound_from_singular_coordinate_energies
-- name    : tangent_coordinate_kernel_diagonal_bound_from_singular_coordinate_energies
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T17:05:16.685673+00:00
-- url     : https://prove2.me/theorems/5a3da5ec-9841-4188-8e91-d4743887e833
-- statement:
--   This lemma converts singular-coordinate energy bounds into the diagonal tangent-coordinate kernel estimate.
--
--   For a coordinate $\omega=(i,j)$, the diagonal tangent kernel is
--   $$
--   P_{\omega\omega}=\langle P_T(e_i e_j^\top),e_i e_j^\top\rangle.
--   $$
--   Using the explicit tangent projection formula, it is bounded from the coordinate energies of the left and right singular-vector spaces. If A0 supplies the scales $\mu_0 r/n_1$ and $\mu_0 r/n_2$, and Bessel bounds both energies by $1$, then
--   $$
--   |P_{\omega\omega}|\le C {\mu_0 r\over \min(n_1,n_2)}.
--   $$
--
--   Source: Candes-Recht 2008, PDF p. 23, estimate (6.2), with the rectangular-scale convention stated after PDF p. 24, estimates (6.2)--(6.4).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem tangent_coordinate_kernel_diagonal_bound_from_singular_coordinate_energies :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ →
        (∀ i : Fin n₁,
          ∑ k : Fin r, (S.u k i) ^ 2 ≤ μ₀ * (r : ℝ) / (n₁ : ℝ)) →
        (∀ j : Fin n₂,
          ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₀ * (r : ℝ) / (n₂ : ℝ)) →
        (∀ i : Fin n₁, ∑ k : Fin r, (S.u k i) ^ 2 ≤ (1 : ℝ)) →
        (∀ j : Fin n₂, ∑ k : Fin r, (S.v k j) ^ 2 ≤ (1 : ℝ)) →
        ∀ i j,
          |tangentCoordinateKernel S i j i j| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  sorry

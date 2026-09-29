-- Prove2me | solution 1 for linear_neumann_diagonal_base_entry_sup_norm_bound_by_sign_entry_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T19:09:24.665286+00:00
-- url     : https://prove2.me/submissions/1f57f739-b9fd-4241-be9f-779aacbd694d

import Mathlib.Tactic
import Theorems.Thm_entry_sup_norm_tangent_diagonal_multiplier_bound_from_kernel_bound
import Theorems.Thm_tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim

open MatrixCompletion

/--
Source: Candes-Recht 2008, PDF p. 23, estimate (6.2), PDF p. 26, equation
(6.9), and Lemma 6.4/equations (6.10)--(6.11).  The rectangular scale is the
`min(n₁,n₂)` version used after passing from the square exposition to
rectangular matrices.

Reduce the diagonal Neumann base-matrix entry bound to the corrected A0
diagonal tangent-kernel estimate and the generic entry-sup multiplier lemma.
-/
theorem solution :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        entrySupNorm (linearNeumannDiagonalBaseMatrix S) ≤
          Cbase * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) *
            entrySupNorm (signMatrix S) := by
  rcases tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim with
    ⟨Cker, hCker_pos, hker⟩
  refine ⟨Cker, hCker_pos, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  let a : ℝ := Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hbound :
      entrySupNorm (tangentDiagonalMultiplier S (signMatrix S)) ≤
        a * entrySupNorm (signMatrix S) :=
    entry_sup_norm_tangent_diagonal_multiplier_bound_from_kernel_bound
      hn₁ hn₂ S (signMatrix S) ha_nonneg
      (hker n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0)
  simpa [linearNeumannDiagonalBaseMatrix, a, mul_assoc] using hbound

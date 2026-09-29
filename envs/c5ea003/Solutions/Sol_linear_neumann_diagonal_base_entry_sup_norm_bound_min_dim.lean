-- Prove2me | solution 1 for linear_neumann_diagonal_base_entry_sup_norm_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T19:10:47.694102+00:00
-- url     : https://prove2.me/submissions/ff81e842-74d4-496e-8c01-33665b9bf72a

import Mathlib.Tactic
import Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a1
import Theorems.Thm_linear_neumann_diagonal_base_entry_sup_norm_bound_by_sign_entry_min_dim

open MatrixCompletion

/--
Source: Candes-Recht 2008, PDF p. 23, estimate (6.2), PDF p. 26, equation
(6.9), and Lemma 6.4/equations (6.10)--(6.11).  This is the rectangular-safe
version of the diagonal base-entry estimate, with the A0 tangent-kernel factor
at scale `μ₀ r / min(n₁,n₂)` and the A1 sign-entry factor.

Combine the factored diagonal-base entry bound with the A1 entry-sup bound for
the sign matrix.
-/
theorem solution :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        entrySupNorm (linearNeumannDiagonalBaseMatrix S) ≤
          Cbase * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  rcases linear_neumann_diagonal_base_entry_sup_norm_bound_by_sign_entry_min_dim with
    ⟨Cbase, hCbase_pos, hbase⟩
  refine ⟨Cbase, hCbase_pos, ?_⟩
  intro n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ _hμ₁ hA0 hA1
  have hsign := entry_sup_norm_sign_matrix_bound_from_a1 hn₁ hn₂ μ₁ S hA1
  have hbase' := hbase n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  have hfactor_nonneg : 0 ≤ Cbase * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
    positivity
  calc
    entrySupNorm (linearNeumannDiagonalBaseMatrix S)
        ≤ Cbase * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) *
            entrySupNorm (signMatrix S) := hbase'
    _ ≤ Cbase * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) *
          (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left hsign hfactor_nonneg
    _ = Cbase * μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by ring

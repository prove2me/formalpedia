-- Prove2me | solution 1 for bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T22:45:26.899378+00:00
-- url     : https://prove2.me/submissions/da82c981-552e-4640-bc34-c5da2d3b6ce0

import Theorems.Thm_bernoulli_uniform_coordinate_bound_from_pointwise_tails_with_cardinality_factor
import Theorems.Thm_coordinate_cardinality_loss_absorbed_by_beta_shift

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF p. 29, the union-bound step after equation
(6.17), in the coefficient-uniformization argument following Lemma 6.6.  This
is a formal repair of the old no-loss coordinate-uniformization theorem: the
finite coordinate union bound contributes an explicit `n^2` factor, absorbed
here by asking the pointwise tails at exponent `β + 2`. -/
theorem solution
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∃ Cuniform cuniform : ℝ, 0 < Cuniform ∧ 0 < cuniform ∧
      ∀ (β p scale : ℝ), 2 < β → 0 ≤ p → p ≤ 1 →
      ∀ (n₁ n₂ : ℕ),
        0 < n₁ → 0 < n₂ →
        ∀ Coeff : (Fin n₁ × Fin n₂) →
          Finset (Fin n₁ × Fin n₂) → ℝ,
        (∀ w : Fin n₁ × Fin n₂,
          bernoulliEventProb p
              (fun Omega => |Coeff w Omega| ≤ Cpoint * scale) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2))) →
        bernoulliEventProb p
            (fun Omega =>
              ∀ w : Fin n₁ × Fin n₂,
                |Coeff w Omega| ≤ Cuniform * scale) ≥
          1 - cuniform * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCpoint hcpoint
  refine ⟨Cpoint, cpoint, hCpoint, hcpoint, ?_⟩
  intro β p scale hβ hp_nonneg hp_le_one n₁ n₂ hn₁ hn₂ Coeff hPointwise
  have hUniform :=
    bernoulli_uniform_coordinate_bound_from_pointwise_tails_with_cardinality_factor
      Cpoint cpoint hCpoint hcpoint p scale
      (Real.rpow (↑(max n₁ n₂)) (-(β + 2)))
      hp_nonneg hp_le_one n₁ n₂ Coeff hPointwise
  have hLoss :=
    coordinate_cardinality_loss_absorbed_by_beta_shift
      β cpoint n₁ n₂ hβ hcpoint hn₁ hn₂
  have hTail :
      1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) ≤
        1 -
          (((Fintype.card (Fin n₁ × Fin n₂) : ℝ) * cpoint) *
            Real.rpow (↑(max n₁ n₂)) (-(β + 2))) := by
    linarith
  exact le_trans hTail hUniform

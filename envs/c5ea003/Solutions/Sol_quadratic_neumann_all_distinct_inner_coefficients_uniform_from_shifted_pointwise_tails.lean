-- Prove2me | solution 1 for quadratic_neumann_all_distinct_inner_coefficients_uniform_from_shifted_pointwise_tails
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T22:31:12.99018+00:00
-- url     : https://prove2.me/submissions/3316cb05-140c-40b7-8e54-cd9d3b9e4648

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
import Theorems.Thm_pair_coordinate_cardinality_loss_absorbed_by_beta_shift
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF p. 28, Lemma 6.6 and equation (6.15),
PDF p. 29, the union-bound step after equation (6.17), and PDF p. 30,
equation (6.20), where the all-distinct quadratic Neumann term is split into
coordinate-pair coefficient events.  This is a formal repair of the old
no-loss uniformization sketch: the finite ordered-pair union bound contributes
an explicit `n^4` cardinality factor, absorbed here by asking the pointwise
tails at exponent `β + 4`. -/
theorem solution
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∃ Cinner cinner : ℝ, 0 < Cinner ∧ 0 < cinner ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega3 =>
                |quadraticAllDistinctInnerCoefficient Omega3 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2| ≤
                  Cpoint * Real.rpow lam (-((1 : ℝ) / 2))) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 4))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cinner * Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCpoint hcpoint
  refine ⟨Cpoint, cpoint, hCpoint, hcpoint, ?_⟩
  intro β lam hβ _hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ _hr hm _hμ₀ _hμ₁ _hA0 _hA1 _hmLower hPointwise
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hp_nonneg, hp_le_one⟩
  have hUniform :=
    bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
      Cpoint cpoint hCpoint hcpoint
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
      (Real.rpow lam (-((1 : ℝ) / 2)))
      (Real.rpow (↑(max n₁ n₂)) (-(β + 4)))
      hp_nonneg hp_le_one n₁ n₂
      (fun w1 w2 Omega3 =>
        quadraticAllDistinctInnerCoefficient Omega3 S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2)
      hPointwise
  have hLoss :=
    pair_coordinate_cardinality_loss_absorbed_by_beta_shift
      β cpoint n₁ n₂ hβ hcpoint hn₁ hn₂
  have hTail :
      1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) ≤
        1 -
          (((Fintype.card
            ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) *
            cpoint) *
            Real.rpow (↑(max n₁ n₂)) (-(β + 4))) := by
    linarith
  exact le_trans hTail (by
    simpa [QuadraticAllDistinctInnerCoefficientBound] using hUniform)

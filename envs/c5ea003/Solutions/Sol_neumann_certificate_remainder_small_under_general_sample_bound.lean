-- Prove2me | solution 1 for neumann_certificate_remainder_small_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:09:23.470026+00:00
-- url     : https://prove2.me/submissions/dcb89941-3208-4975-ab7b-ca76ed568a28

import Theorems.Thm_neumann_certificate_remainder_small_with_explicit_formula
import Theorems.Thm_neumann_certificate_remainder_formula_bound_from_general_bound
import Theorems.Thm_bernoulli_neumann_certificate_tail_bound_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Decompose the theorem-regime Neumann remainder estimate through the explicit
Lemma 4.8 formula and a separate sample-arithmetic absorption step. -/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              NeumannCertificateTailSpectralBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 3 ((1 : ℝ) / 2)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases neumann_certificate_remainder_small_with_explicit_formula with
    ⟨CR, Ctail, ctail, _hCR, _hCtail, hctail, hLemma48⟩
  rcases neumann_certificate_remainder_formula_bound_from_general_bound CR Ctail with
    ⟨C, hC, hAbsorb⟩
  refine ⟨C, ctail, hC, hctail, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  rcases hAbsorb C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower with
    ⟨hLemmaSample, hFormulaBound⟩
  have hProb :=
    hLemma48 β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hLemmaSample
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  exact bernoulli_neumann_certificate_tail_bound_probability_mono S
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 3
    (neumannRemainderFormulaBound Ctail β μ₀ (max n₁ n₂) r m)
    ((1 : ℝ) / 2) ctail β hpNonneg hpLeOne hFormulaBound hProb


-- Prove2me | solution 1 for candes_recht_theorem41_bernoulli_tangent_sampling_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T02:51:42.831095+00:00
-- url     : https://prove2.me/submissions/015ac9eb-0664-432f-85f4-e16f48750b0c

import Theorems.Thm_candes_recht_theorem42_tangent_sampling_deviation_bound_with_sample_constant
import Theorems.Thm_neumann_remainder_tangent_scale_le_half_from_sample_bound
import Theorems.Thm_bernoulli_tangent_sampling_concentration_from_deviation_bound
import Theorems.Thm_bernoulli_tangent_sampling_concentration_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candes--Recht, PDF pp. 18--20, Theorem 4.1 and Theorem 4.2,
especially equations (4.5), (4.9), and (4.10).

The child theorem packages the paper's Theorem 4.2 deviation estimate after the
universal sample constant has been chosen large enough to satisfy both smallness
provisos: the Rudelson expectation RHS in (4.9) is below `1`, and hence the
Talagrand concentration estimate (4.10), which assumes `E Z ≤ 1`, applies.

This sketch performs the remaining deterministic part of Theorem 4.1: choose
the sample constant also large enough that the displayed deviation scale is at
most `1/2`, convert deviation control into tangent concentration, and enlarge
the concentration radius by Bernoulli event monotonicity.
-/
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
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingConcentration Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ((1 : ℝ) / 2)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases candes_recht_theorem42_tangent_sampling_deviation_bound_with_sample_constant with
    ⟨Cdev, cdev, hCdev, hcdev, hDeviation⟩
  rcases neumann_remainder_tangent_scale_le_half_from_sample_bound Cdev with
    ⟨Cscale, hCscale, hScaleSmall⟩
  let C : ℝ := max (max Cdev Cscale) 1
  have hC_pos : 0 < C :=
    lt_of_lt_of_le hCdev (le_trans (le_max_left Cdev Cscale) (le_max_left _ 1))
  refine ⟨C, cdev, hC_pos, hcdev, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ _hμ₁ hA0 _hA1 hmLower
  let n : ℕ := max n₁ n₂
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hCdev_le_C' : Cdev ≤ C' := by
    exact le_trans (le_trans (le_max_left Cdev Cscale) (le_max_left _ 1)) hC'
  have hCscale_le_C' : Cscale ≤ C' := by
    exact le_trans (le_trans (le_max_right Cdev Cscale) (le_max_left _ 1)) hC'
  have hn : 0 < n := by
    dsimp [n]
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hn_real_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hβ_nonneg : 0 ≤ β :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 2) hβ)
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg hn_real_ge_one
  have htail_nonneg :
      0 ≤ μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ)) := by
    positivity
  have hCscaleLower :
      (m : ℝ) ≥ Cscale * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ)) := by
    have hle :
        Cscale * (μ₀ * (n : ℝ) * (r : ℝ) *
            (β * Real.log (n : ℝ))) ≤
          C' * (μ₀ * (n : ℝ) * (r : ℝ) *
            (β * Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hCscale_le_C' htail_nonneg
    calc
      Cscale * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ))
          = Cscale * (μ₀ * (n : ℝ) * (r : ℝ) *
              (β * Real.log (n : ℝ))) := by ring
      _ ≤ C' * (μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ))) := hle
      _ = C' * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ)) := by ring
      _ ≤ (m : ℝ) := by
        simpa [n, C, mul_assoc] using hmLower
  have hDeviationProb :
      bernoulliEventProb p
          (fun Omega =>
            TangentSamplingDeviationBound Omega S p
              (tangentSamplingDeviationScale Cdev β μ₀ n r m)) ≥
        1 - cdev * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa [p, n] using
      hDeviation C' hCdev_le_C' β hβ n₁ n₂ r m M μ₀ S
        hn₁ hn₂ hr hm hμ₀ hA0 hmLower
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  have hConcentrationAtScale :
      bernoulliEventProb p
          (fun Omega =>
            TangentSamplingConcentration Omega S p
              (tangentSamplingDeviationScale Cdev β μ₀ n r m)) ≥
        1 - cdev * Real.rpow (↑(max n₁ n₂)) (-β) :=
    bernoulli_tangent_sampling_concentration_from_deviation_bound S p
      (tangentSamplingDeviationScale Cdev β μ₀ n r m) cdev β
      hpNonneg hpLeOne hDeviationProb
  have hScale :
      tangentSamplingDeviationScale Cdev β μ₀ n r m ≤ (1 : ℝ) / 2 :=
    hScaleSmall β hβ n r m μ₀ hn hr hμ₀ hCscaleLower
  exact bernoulli_tangent_sampling_concentration_probability_mono S p
    (tangentSamplingDeviationScale Cdev β μ₀ n r m) ((1 : ℝ) / 2)
    cdev β hpNonneg hpLeOne hScale hConcentrationAtScale

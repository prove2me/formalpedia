-- Prove2me | solution 1 for neumann_remainder_sample_bound_gives_scale_and_dense_concentration_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T04:41:41.770158+00:00
-- url     : https://prove2.me/submissions/e4cb8b92-938f-4b77-8270-bbc79eb20c7a

import Theorems.Thm_neumann_remainder_tangent_scale_le_half_from_sample_bound
import Mathlib.Tactic

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF pp. 18-21, Theorem 4.1/Theorem 4.2 and
Lemma 4.8.  This scalar reduction chooses the Lemma 4.8 sample constant large
enough to also dominate the dense tangent-concentration lower bound. -/
theorem solution
    (Cdev : ℝ) :
    ∃ CR : ℝ, 0 < CR ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n r m : ℕ) (μ₀ : ℝ),
        0 < n → 0 < r → 1 ≤ μ₀ →
        (m : ℝ) ≥ CR * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ)) →
        tangentSamplingDeviationScale Cdev β μ₀ n r m ≤ (1 : ℝ) / 2 ∧
          (m : ℝ) ≥ β * μ₀ * (n : ℝ) * (r : ℝ) *
            Real.log (n : ℝ) := by
  rcases neumann_remainder_tangent_scale_le_half_from_sample_bound Cdev with
    ⟨Cscale, hCscale, hScale⟩
  let CR : ℝ := max Cscale 1
  refine ⟨CR, lt_of_lt_of_le hCscale (le_max_left Cscale 1), ?_⟩
  intro β hβ n r m μ₀ hn hr hμ₀ hmLower
  let B : ℝ := μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ))
  have hβ_nonneg : 0 ≤ β := by linarith
  have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
  have hn_one_nat : 1 ≤ n := Nat.succ_le_of_lt hn
  have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_one_nat
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_one
  have hβlog_nonneg : 0 ≤ β * Real.log (n : ℝ) :=
    mul_nonneg hβ_nonneg hlog_nonneg
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hCscale_le_CR : Cscale ≤ CR := le_max_left Cscale 1
  have hOne_le_CR : (1 : ℝ) ≤ CR := le_max_right Cscale 1
  have hScaleLower :
      (m : ℝ) ≥ Cscale * μ₀ * (n : ℝ) * (r : ℝ) *
        (β * Real.log (n : ℝ)) := by
    have hle : Cscale * B ≤ CR * B :=
      mul_le_mul_of_nonneg_right hCscale_le_CR hB_nonneg
    calc
      Cscale * μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ))
          = Cscale * B := by ring
      _ ≤ CR * B := hle
      _ = CR * μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ)) := by ring
      _ ≤ (m : ℝ) := hmLower
  have hDenseLower :
      (m : ℝ) ≥ β * μ₀ * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ) := by
    have hle : (1 : ℝ) * B ≤ CR * B :=
      mul_le_mul_of_nonneg_right hOne_le_CR hB_nonneg
    calc
      β * μ₀ * (n : ℝ) * (r : ℝ) * Real.log (n : ℝ)
          = (1 : ℝ) * B := by ring
      _ ≤ CR * B := hle
      _ = CR * μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ)) := by ring
      _ ≤ (m : ℝ) := hmLower
  exact ⟨hScale β hβ n r m μ₀ hn hr hμ₀ hScaleLower, hDenseLower⟩

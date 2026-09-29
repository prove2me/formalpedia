-- Prove2me | solution 1 for talagrand_tangent_sampling_raw_tail_le_deviation_scale
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-24T18:57:37.018053+00:00
-- url     : https://prove2.me/submissions/c61b2eef-a202-4ddc-91cf-c268fed56d66

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators

namespace ProveTalagrandScalar

theorem sqrt_two_mul_le_two_sqrt (A : ℝ) (hA : 0 ≤ A) :
    Real.sqrt (2 * A) ≤ 2 * Real.sqrt A := by
  have hleft0 : 0 ≤ Real.sqrt (2 * A) := Real.sqrt_nonneg _
  have hright0 : 0 ≤ 2 * Real.sqrt A := by positivity
  have hsquare : (Real.sqrt (2 * A)) ^ 2 ≤ (2 * Real.sqrt A) ^ 2 := by
    rw [Real.sq_sqrt]
    · rw [mul_pow, Real.sq_sqrt hA]
      nlinarith [hA]
    · positivity
  nlinarith

end ProveTalagrandScalar

open ProveTalagrandScalar

theorem solution
    (K : ℝ) :
    0 < K →
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ →
        K * Real.sqrt
            ((2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) *
              (β * Real.log (↑(max n₁ n₂)))) ≤
          tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m := by
  intro hK
  refine ⟨2 * K, by positivity, ?_⟩
  intro β hβ n₁ n₂ r m μ₀ hn₁ _hn₂ _hr hμ₀
  simp only [tangentSamplingDeviationScale]
  have hmax_pos : 0 < max n₁ n₂ :=
    lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hmax_ge_one_nat : 1 ≤ max n₁ n₂ := Nat.succ_le_of_lt hmax_pos
  have hmax_ge_one : (1 : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by
    exact_mod_cast hmax_ge_one_nat
  have hlog_nonneg : 0 ≤ Real.log (↑(max n₁ n₂) : ℝ) :=
    Real.log_nonneg hmax_ge_one
  have hβ_nonneg : 0 ≤ β := by linarith
  have hμ₀_nonneg : 0 ≤ μ₀ := by linarith
  set A : ℝ :=
    (μ₀ * (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
        (β * Real.log (↑(max n₁ n₂) : ℝ))) / (m : ℝ) with hAdef
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]
    positivity
  have harg :
      ((2 * μ₀ * (↑(max n₁ n₂) : ℝ) * (r : ℝ) / (m : ℝ)) *
          (β * Real.log (↑(max n₁ n₂) : ℝ))) = 2 * A := by
    rw [hAdef]
    ring
  calc
    K * Real.sqrt
        ((2 * μ₀ * (↑(max n₁ n₂) : ℝ) * (r : ℝ) / (m : ℝ)) *
          (β * Real.log (↑(max n₁ n₂) : ℝ)))
        = K * Real.sqrt (2 * A) := by rw [harg]
    _ ≤ K * (2 * Real.sqrt A) := by
        exact mul_le_mul_of_nonneg_left
          (sqrt_two_mul_le_two_sqrt A hA_nonneg) (le_of_lt hK)
    _ = (2 * K) *
        Real.sqrt
          ((μ₀ * (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂) : ℝ))) / (m : ℝ)) := by
        rw [hAdef]
        ring

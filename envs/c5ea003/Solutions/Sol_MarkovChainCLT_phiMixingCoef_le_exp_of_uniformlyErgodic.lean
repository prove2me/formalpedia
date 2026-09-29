-- Prove2me | solution 1 for MarkovChainCLT.phiMixingCoef_le_exp_of_uniformlyErgodic
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T21:23:05.583733+00:00
-- url     : https://prove2.me/submissions/de442b7a-28f7-44a8-85ca-a3882f82fc8c

import Theorems.Thm_MarkovChainCLT_phiMixingCoef_le_of_tvDist_le

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

set_option maxHeartbeats 1000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (huni : UniformlyErgodic P π) :
    ∃ c θ : ℝ, 0 ≤ c ∧ 0 < θ ∧ ∀ n : ℕ, 1 ≤ n →
      phiMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n
        ≤ c * Real.exp (-θ * n) := by
  obtain ⟨R, t, hR, ht0, ht1, hrate⟩ := huni
  -- replace `t` by `t' = max t (1/2)`, which is bounded away from `0`
  set t' : ℝ := max t (1 / 2) with ht'
  have ht'pos : 0 < t' := lt_of_lt_of_le (by norm_num) (le_max_right t (1 / 2))
  have ht'lt : t' < 1 := max_lt ht1 (by norm_num)
  have htt' : t ≤ t' := le_max_left t (1 / 2)
  set θ : ℝ := -Real.log t' with hθ
  have hθpos : 0 < θ := by
    have : Real.log t' < 0 := Real.log_neg ht'pos ht'lt
    simpa [hθ] using this
  refine ⟨R, θ, hR, hθpos, fun n hn => ?_⟩
  -- the exponential form of `t'^n`
  have hexp : Real.exp (-θ * n) = t' ^ n := by
    have h1 : -θ * (n : ℝ) = (n : ℝ) * Real.log t' := by rw [hθ]; ring
    rw [h1, Real.exp_nat_mul, Real.exp_log ht'pos]
  -- the total-variation rate at lag `n`
  have hC : ∀ x, tvDist ((iterKernel P n) x) π ≤ R * Real.exp (-θ * n) := by
    intro x
    have h := hrate x n hn
    have hpow : t ^ n ≤ t' ^ n := by gcongr
    rw [hexp]
    calc tvDist ((iterKernel P n) x) π ≤ R * t ^ n := h
      _ ≤ R * t' ^ n := by exact mul_le_mul_of_nonneg_left hpow hR
  have hC0 : 0 ≤ R * Real.exp (-θ * n) := by positivity
  exact MarkovChainCLT.phiMixingCoef_le_of_tvDist_le P π hinv n hn _ hC0 hC

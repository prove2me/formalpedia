-- Prove2me | solution 1 for MarkovChainCLT.exists_lag_tvDist_le_of_uniformlyErgodic
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T01:23:51.375765+00:00
-- url     : https://prove2.me/submissions/c788480e-c915-41ea-bc54-4494b549da8d

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution {X : Type*} [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) (huni : UniformlyErgodic P π) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ x, tvDist (iterKernel P N x) π ≤ 1 / 16 := by
  obtain ⟨R, t, hR, ht0, ht1, hrate⟩ := huni
  have hlim : Tendsto (fun n : ℕ => R * t ^ n) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1
    have := h.const_mul R
    simpa using this
  have hev : ∀ᶠ n : ℕ in atTop, R * t ^ n ≤ 1 / 16 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1 / 16))
  obtain ⟨N0, hN0⟩ := hev.exists_forall_of_atTop
  refine ⟨N0 + 1, by omega, fun x => ?_⟩
  exact le_trans (hrate x (N0 + 1) (by omega)) (hN0 (N0 + 1) (by omega))

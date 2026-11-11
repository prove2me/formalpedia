-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_bound_of_exponent
-- name    : levy_foundations_public_semigroup_scaled_largeSet_bound_of_exponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:19:56.202946+00:00
-- url     : https://prove2.me/theorems/3c38d09e-e770-43b0-a4a6-1e080b2703f1
-- title:
--   M5 scaled large-jump bound under a prescribed low-frequency exponent bound
-- statement:
--   Whenever the exponent norm on the frequency interval [0,2/ε] is bounded by a prescribed C, the scaled semigroup mass of {|x|≥ε} is at most 4C at every positive time. It makes the Fourier-smoothed mass estimate quantitatively usable for the tail-tightness argument by choosing C arbitrarily small from continuity at zero.
-- source:
--   Sharp source-faithful variant of accepted candidate 32805: the original proof bounds scaled mass by 4*max_{[0,2/ε]}‖ψ‖, then uses hC at the maximiser. It feeds uniform tail tightness needed by Lévy-measure Prokhorov extraction a407ec20-f0b2-46a7-a269-5aaad3eb2279.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_largeSet_cosine_interval_lower_bound
import Theorems.Thm_levy_foundations_public_semigroup_scaled_exponential_real_norm_bound
import Theorems.Thm_levy_foundations_public_cosine_interval_integral_swap
import Theorems.Thm_levy_foundations_public_semigroup_real_deficit_cosine_integral
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal

theorem levy_foundations_public_semigroup_scaled_largeSet_bound_of_exponent
    (S : ProbabilityTheory.ConvolutionSemigroup)
    (ε : ℝ) (hε : 0 < ε) (C : ℝ)
    (hC : ∀ ξ ∈ Set.Icc (0 : ℝ) (2 / ε), ‖S.exponent ξ‖ ≤ C) :
    ∀ t : {t : ℝ // 0 < t},
      t.val⁻¹ * ((S.measure t : Measure ℝ) (largeSet ε)).toReal ≤ 4 * C := by sorry

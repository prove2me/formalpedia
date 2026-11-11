-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_sharp
-- name    : levy_foundations_public_semigroup_scaled_largeSet_sharp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:16:01.129909+00:00
-- url     : https://prove2.me/theorems/d36c65b7-3cad-4526-a949-d6eb8fc4a89c
-- title:
--   M5 sharp scaled large-jump mass bound by low-frequency exponent
-- statement:
--   For each jump threshold ε, one can choose an upper bound M for the exponent norm on frequencies [0,2/ε], and the semigroup's scaled probability of a jump at least ε is bounded by 4M for every positive time. Unlike the earlier C=4M+1 estimate, the constant vanishes with M and therefore yields tightness of the scaled large-jump tails as ε grows.
-- source:
--   Exact strengthening of previously accepted large-set mass proof 32805, derived by retaining its verified final 4*M inequality before the unnecessary +1 slack. Prerequisite for scaled tail tightness in M5 Lévy-measure extraction a407ec20-f0b2-46a7-a269-5aaad3eb2279.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_largeSet_cosine_interval_lower_bound
import Theorems.Thm_levy_foundations_public_semigroup_scaled_exponential_real_norm_bound
import Theorems.Thm_levy_foundations_public_cosine_interval_integral_swap
import Theorems.Thm_levy_foundations_public_semigroup_real_deficit_cosine_integral
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal

theorem levy_foundations_public_semigroup_scaled_largeSet_sharp
    (S : ProbabilityTheory.ConvolutionSemigroup)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ,
      (∀ ξ ∈ Set.Icc (0 : ℝ) (2 / ε), ‖S.exponent ξ‖ ≤ M) ∧
      ∀ t : {t : ℝ // 0 < t},
        t.val⁻¹ * ((S.measure t : Measure ℝ) (largeSet ε)).toReal ≤ 4 * M := by sorry

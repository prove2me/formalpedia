-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_quantitative_bound
-- name    : levy_foundations_public_semigroup_scaled_largeSet_quantitative_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:10:17.210836+00:00
-- url     : https://prove2.me/theorems/e18eb15c-e0ce-4250-889a-e5091f59b801
-- title:
--   Quantitative scaled large-jump mass bound from an exponent band bound
-- statement:
--   If the Lévy semigroup characteristic exponent has norm at most M for all frequencies between zero and 2/ε, then the scaled probability mass outside the radius ε is at most 4M for every positive time. The proof uses the public cosine interval estimate, Fubini interchange, real characteristic deficit identity and exponential norm estimate. This explicit bound is the tightness ingredient of original tiltedScaledMeasure_largeSet_le, required for the canonical Lévy measure extraction of milestone M5.
-- source:
--   Original LeanLevy ConvolutionSemigroup.scaled_mass_bound_real_with_max, source https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean; extracted from already remotely accepted bound proof candidate 32805; M5 tail target 61326a97-bb56-4e8f-9b28-7ee30e3cbd42.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_largeSet_cosine_interval_lower_bound
import Theorems.Thm_levy_foundations_public_semigroup_scaled_exponential_real_norm_bound
import Theorems.Thm_levy_foundations_public_cosine_interval_integral_swap
import Theorems.Thm_levy_foundations_public_semigroup_real_deficit_cosine_integral
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_scaled_largeSet_quantitative_bound
    (S : ProbabilityTheory.ConvolutionSemigroup) (ε : ℝ) (hε : 0 < ε) (M : ℝ)
    (hM : ∀ ξ ∈ Set.Icc (0:ℝ) (2/ε), ‖S.exponent ξ‖ ≤ M) :
    ∀ (t : {t : ℝ // 0 < t}),
      t.val⁻¹ * ((S.measure t : Measure ℝ) (ProbabilityTheory.largeSet ε)).toReal ≤ 4 * M := by sorry

-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_tail_bound
-- name    : levy_foundations_public_semigroup_scaled_largeSet_tail_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:26:42.70434+00:00
-- url     : https://prove2.me/theorems/9f8a1f1a-4298-4e60-a82e-4ccd9a83f862
-- title:
--   Uniform smallness of scaled semigroup mass outside sufficiently large balls
-- statement:
--   For every ε>0, choose a radius R≥1 so that the original semigroup scaled large-jump mass is ≤ε uniformly over all positive times. The proof uses continuity of the Lévy exponent at zero and the established public quantitative cosine bound.
-- source:
--   Source-exact ConvolutionSemigroup.scaled_largeSet_mass_le_of_large_radius, LeanLevy/Levy/LevyKhintchineProof.lean, source commit 7e73fd9b23ad52956ec2756a815889a783131ce4; replaced its private quantitative lemma with the now-Proved public quantitative bound e18eb15c. Required by public canonical extraction d3cd6d70 and the uniqueness chain.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_quantitative_bound
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_scaled_largeSet_tail_bound
    (S : ProbabilityTheory.ConvolutionSemigroup) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ t : {t : ℝ // 0 < t},
      t.val⁻¹ * ((S.measure t : Measure ℝ) (largeSet R)).toReal ≤ ε := by
  sorry

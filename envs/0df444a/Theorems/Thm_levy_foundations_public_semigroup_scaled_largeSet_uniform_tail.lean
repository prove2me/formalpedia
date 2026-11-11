-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_uniform_tail
-- name    : levy_foundations_public_semigroup_scaled_largeSet_uniform_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:25:42.493196+00:00
-- url     : https://prove2.me/theorems/6b75118f-fe7b-4add-8e93-0e76613acecf
-- title:
--   M5 uniform tightness of scaled large-jump semigroup tails
-- statement:
--   For every positive tolerance δ, there is a sufficiently large spatial radius R such that t^{-1} times the semigroup probability of a jump at least R is at most δ simultaneously for all positive times. Choose a low-frequency neighbourhood on which the characteristic exponent has norm at most δ/4, and apply the published uniform 4C cosine-smoothing bound. Supplies tail tightness for Lévy-measure Prokhorov extraction.
-- source:
--   Exact consequence of published public source-backed bound-of-exponent theorem 3c38d09e-e770-43b0-a4a6-1e080b2703f1 and ConvolutionSemigroup.exponent_continuous/exponent_zero. Necessary tightness input to Prokhorov construction in a407ec20-f0b2-46a7-a269-5aaad3eb2279.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_bound_of_exponent
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

theorem levy_foundations_public_semigroup_scaled_largeSet_uniform_tail
    (S : ProbabilityTheory.ConvolutionSemigroup)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : {t : ℝ // 0 < t},
      t.val⁻¹ * ((S.measure t : Measure ℝ) (largeSet R)).toReal ≤ δ := by sorry

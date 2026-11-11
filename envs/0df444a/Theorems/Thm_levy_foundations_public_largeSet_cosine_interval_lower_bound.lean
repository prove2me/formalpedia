-- Prove2me | Theorems.Thm_levy_foundations_public_largeSet_cosine_interval_lower_bound
-- name    : levy_foundations_public_largeSet_cosine_interval_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T12:19:40.078196+00:00
-- url     : https://prove2.me/theorems/efe87ad9-c067-4bde-afde-55e1aa0f4c6a
-- title:
--   Fourier cosine interval lower bound away from the origin
-- statement:
--   For a nonzero x with absolute value at least ε, the frequency average ∫ from 0 to 2/ε of (1-cos(ξx)) is at least 1/ε. This is the crucial pointwise Fourier-smoothing estimate from LeanLevy scaled_mass_bound_real, needed to control large-set jump mass and finish the M5 drift eventual boundedness proof.
-- source:
--   Original LeanLevy LevyKhintchineProof.lean private ConvolutionSemigroup.scaled_mass_bound_real, hpointwise; https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean . Root-connected public M5 parent 0fe64c60-e8fd-49af-b662-5e82d1c7dc5a.

import Mathlib.Probability.Independence.CharacteristicFunction
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_largeSet_cosine_interval_lower_bound
    (ε : ℝ) (hε : 0 < ε) (x : ℝ) (hx : ε ≤ |x|) :
    ε⁻¹ ≤ ∫ ξ in (0 : ℝ)..(2 / ε), (1 - Real.cos (ξ * x)) := by sorry

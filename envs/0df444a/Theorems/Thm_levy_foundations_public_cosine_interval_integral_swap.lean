-- Prove2me | Theorems.Thm_levy_foundations_public_cosine_interval_integral_swap
-- name    : levy_foundations_public_cosine_interval_integral_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T12:25:12.628543+00:00
-- url     : https://prove2.me/theorems/a4693483-615d-42b2-adb3-758620680a5f
-- title:
--   Fubini swap for the frequency-averaged cosine deficit
-- statement:
--   For a probability measure, the bounded nonnegative cosine deficit is integrable on the finite frequency interval times the real line. Its integrals may therefore be exchanged. This is the Fubini step of the original LeanLevy semigroup scaled large-set mass estimate, one of the dependencies needed to close the M5 drift bound.
-- source:
--   LeanLevy LevyKhintchineProof.lean, ConvolutionSemigroup.scaled_mass_bound_real, hfubini_int and hfubini. https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean . M5 drift root-connected parent 0fe64c60-e8fd-49af-b662-5e82d1c7dc5a.

import Mathlib.Probability.Independence.CharacteristicFunction
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_cosine_interval_integral_swap
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ε : ℝ) (hε : 0 < ε) :
    (∫ ξ in (0 : ℝ)..(2 / ε), ∫ x, (1 - Real.cos (ξ * x)) ∂μ) =
      ∫ x, (∫ ξ in (0 : ℝ)..(2 / ε), (1 - Real.cos (ξ * x))) ∂μ := by sorry

-- Prove2me | Theorems.Thm_levy_foundations_public_finite_measure_untilting
-- name    : levy_foundations_public_finite_measure_untilting
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T13:44:46.232099+00:00
-- url     : https://prove2.me/theorems/fa517d6c-afc4-46d4-8d4c-92a78e3cfc0c
-- title:
--   M5 remove quadratic tilt from a finite measure to obtain a Lévy measure
-- statement:
--   For any finite measure η, define ν by the reciprocal min(1,x²) density off the origin, and zero density at the origin. This is a Lévy measure. Every bounded continuous test vanishing near zero divides continuously and boundedly by the weight, with equality of corresponding integrals.
-- source:
--   Untilting component of the public M5 weighted Prokhorov extraction. It isolates the zero-atom and weighted-integrability arguments from weak compactness.

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.Prokhorov
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_finite_measure_untilting
    (η : Measure ℝ) [IsFiniteMeasure η] :
    ∃ ν : Measure ℝ, IsLevyMeasure ν ∧
      ∀ f : BoundedContinuousFunction ℝ ℝ,
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        ∃ g : BoundedContinuousFunction ℝ ℝ,
          g 0 = 0 ∧
          (∀ x : ℝ, f x = min (1 : ℝ) (x ^ 2) * g x) ∧
          (∫ x, f x ∂ν) = ∫ x, g x ∂η := by sorry

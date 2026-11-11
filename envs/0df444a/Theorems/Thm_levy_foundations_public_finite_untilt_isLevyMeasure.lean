-- Prove2me | Theorems.Thm_levy_foundations_public_finite_untilt_isLevyMeasure
-- name    : levy_foundations_public_finite_untilt_isLevyMeasure
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T13:53:25.488671+00:00
-- url     : https://prove2.me/theorems/d319baf9-cedf-4d98-affe-ca67a841655e
-- title:
--   M5 finite measure reciprocal quadratic tilt is a Lévy measure
-- statement:
--   For any finite measure η, multiply η by 1/min(1,x²) using the real convention 0⁻¹=0. The resulting measure has no atom at zero and an integrable Lévy weight min(1,x²), so is a Lévy measure.
-- source:
--   Sound direct constructor for the finite-measure untilting child in the M5 weighted Prokhorov reduction; uses the exact pinned IsLevyMeasure.isLevyMeasure_iff criteria.

import Mathlib.MeasureTheory.Measure.WithDensity
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_finite_untilt_isLevyMeasure
    (η : Measure ℝ) [IsFiniteMeasure η] :
    IsLevyMeasure
      (η.withDensity (fun x : ℝ =>
        ENNReal.ofReal ((min (1 : ℝ) (x ^ 2))⁻¹))) := by sorry

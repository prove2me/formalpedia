-- Prove2me | Theorems.Thm_levy_foundations_public_prob_topup_normalises
-- name    : levy_foundations_public_prob_topup_normalises
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:27:06.460067+00:00
-- url     : https://prove2.me/theorems/2f832c20-b34c-47f5-80c3-698ac7808a56
-- title:
--   A finite measure topped up at zero normalises to a probability measure
-- statement:
--   Given a finite measure ν with total mass at most a strictly positive real Mass, scale ν by 1/Mass and add a Dirac measure at zero weighted by the nonnegative mass deficit. The result has total mass one and is a probability measure. This lemma isolates the normalisation algebra used in the original LeanLevy Prokhorov extraction, so its source can fit within the Prove2Me 150-line limit.
-- source:
--   LeanLevy source theorem ConvolutionSemigroup.exists_canonicalMeasure Step 3. Needed for public conditional Prokhorov child 432dfef2-7c1a-40e1-8d8c-b50ffc2c2ded and original canonical measure target 2a8d84b1-c82c-4941-987b-a4a8a1411f3f.

import Mathlib.Probability.Independence.CharacteristicFunction
open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_prob_topup_normalises
    (ν : Measure ℝ) (Mass : ℝ) (hMass_pos : 0 < Mass)
    (hν_mass : ν Set.univ ≤ ENNReal.ofReal Mass) :
    IsProbabilityMeasure
      ((ENNReal.ofReal Mass⁻¹) • ν +
        (ENNReal.ofReal Mass⁻¹ * (ENNReal.ofReal Mass - ν Set.univ)) •
          Measure.dirac (0 : ℝ)) := by sorry

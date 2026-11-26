-- Prove2me | solution 1 for ReweightedNPMLE.abs_gaussianScore_le
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:52:34.79274+00:00
-- url     : https://prove2.me/submissions/f4dfdc64-42b2-48da-9122-55dd7babfd38

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian

/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

open ReweightedNPMLE
open ReweightedNPMLE in
/-- If `x` and `θ` lie in fixed balls, their Gaussian score is uniformly bounded. -/
theorem solution {d : ℕ} {x θ : Point d} {T S : ℝ}
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hx : ‖x‖ ≤ T) (hθ : ‖θ‖ ≤ S) :
    |gaussianScore x θ| ≤ T * S + S ^ 2 / 2 := by
  have hinner : |inner ℝ x θ| ≤ T * S := by
    exact (abs_real_inner_le_norm x θ).trans
      (mul_le_mul hx hθ (norm_nonneg θ) hT)
  have hsq : ‖θ‖ ^ 2 / 2 ≤ S ^ 2 / 2 := by
    exact div_le_div_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg θ) hS).2 hθ) (by norm_num)
  calc
    |gaussianScore x θ| = |inner ℝ x θ - ‖θ‖ ^ 2 / 2| := rfl
    _ ≤ |inner ℝ x θ| + |‖θ‖ ^ 2 / 2| := abs_sub _ _
    _ = |inner ℝ x θ| + ‖θ‖ ^ 2 / 2 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ ‖θ‖ ^ 2 / 2)]
    _ ≤ T * S + S ^ 2 / 2 := add_le_add hinner hsq

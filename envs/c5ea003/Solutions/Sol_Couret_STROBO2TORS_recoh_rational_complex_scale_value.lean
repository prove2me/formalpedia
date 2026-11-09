-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_rational_complex_scale_value
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:46.887503+00:00
-- url     : https://prove2.me/submissions/23c132ba-ee82-490e-9473-4e02388b45ad

import Definitions.Def_Couret_RecohRationalRoots_2e1442988636
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Couret_RecohRationalComplex_e4146c64164f
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option autoImplicit false

/-!
Rational centres for complex phases, with explicit analytic error bounds.
The centres use Machin's formula and a finite exponential Taylor polynomial.
All finite arithmetic is rational.  The bounds depend on two natural-number
precision parameters, and therefore can be checked without a real comparison.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators























theorem p2m_local_recoh_rational_complex_scale_value (a : ℚ) (z : RecohRationalComplex) :
    recohRationalComplexValue (recohRationalComplexScale a z) =
      (a : ℂ) * recohRationalComplexValue z := by
  apply Complex.ext <;> simp [recohRationalComplexValue, recohRationalComplexScale]



















end Couret.STROBO2TORS


theorem solution : ∀ (a : Rat) (z : Couret.STROBO2TORS.RecohRationalComplex),
  @Eq.{1} Complex (Couret.STROBO2TORS.recohRationalComplexValue (Couret.STROBO2TORS.recohRationalComplexScale a z))
    (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
      (@Rat.cast.{0} Complex Complex.instRatCast a) (Couret.STROBO2TORS.recohRationalComplexValue z)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_rational_complex_scale_value


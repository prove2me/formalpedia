-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_rational_squared_distance_exact
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:51:45.454277+00:00
-- url     : https://prove2.me/submissions/f8be3dfa-817c-423d-a94c-f10394b30c84

import Definitions.Def_Couret_RecohRationalComplex_e4146c64164f
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! Executable rational complex coordinates and their exact norm semantics. -/

namespace Couret.STROBO2TORS







theorem p2m_local_recoh_rational_squared_distance_exact (z w : RecohRationalComplex) :
    ‖recohRationalComplexValue z - recohRationalComplexValue w‖ ^ 2 =
      (recohRationalSquaredDistance z w : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [recohRationalComplexValue, Complex.sub_re, Complex.sub_im,
    recohRationalSquaredDistance, Rat.cast_add, Rat.cast_pow, Rat.cast_sub]
  ring



end Couret.STROBO2TORS


theorem solution : ∀ (z w : Couret.STROBO2TORS.RecohRationalComplex),
  @Eq.{1} Real
    (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid))
      (@Norm.norm.{0} Complex Complex.instNorm
        (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
          (Couret.STROBO2TORS.recohRationalComplexValue z) (Couret.STROBO2TORS.recohRationalComplexValue w)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@Rat.cast.{0} Real Real.instRatCast (Couret.STROBO2TORS.recohRationalSquaredDistance z w)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_rational_squared_distance_exact


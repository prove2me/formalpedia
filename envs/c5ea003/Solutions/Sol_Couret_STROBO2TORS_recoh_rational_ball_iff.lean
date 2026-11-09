-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_rational_ball_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:38.434002+00:00
-- url     : https://prove2.me/submissions/d9b670c3-46c3-49d4-b2f7-983bd2af85ce

import Definitions.Def_Couret_RecohRationalComplex_e4146c64164f
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_squared_distance_exact
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! Executable rational complex coordinates and their exact norm semantics. -/

namespace Couret.STROBO2TORS









/-- Rational squared-distance comparison is exactly the complex closed
ball test, with nonnegative radius made explicit. -/
theorem p2m_local_recoh_rational_ball_iff (z w : RecohRationalComplex)
    (radius : ℚ) (hradius : 0 ≤ radius) :
    recohRationalSquaredDistance z w ≤ radius ^ 2 ↔
      ‖recohRationalComplexValue z - recohRationalComplexValue w‖ ≤ (radius : ℝ) := by
  have hr : 0 ≤ (radius : ℝ) := by exact_mod_cast hradius
  have hs := recoh_rational_squared_distance_exact z w
  constructor
  · intro h
    have hc : (recohRationalSquaredDistance z w : ℝ) ≤ (radius : ℝ) ^ 2 := by
      exact_mod_cast h
    nlinarith [norm_nonneg (recohRationalComplexValue z - recohRationalComplexValue w)]
  · intro h
    have hc : (recohRationalSquaredDistance z w : ℝ) ≤ (radius : ℝ) ^ 2 := by
      rw [← hs]
      exact (sq_le_sq₀ (norm_nonneg _) hr).mpr h
    exact_mod_cast hc

end Couret.STROBO2TORS


theorem solution : ∀ (z w : Couret.STROBO2TORS.RecohRationalComplex) (radius : Rat),
  @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) radius →
    Iff
      (@LE.le.{0} Rat Rat.instLE (Couret.STROBO2TORS.recohRationalSquaredDistance z w)
        (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat (@Monoid.toPow.{0} Rat Rat.monoid)) radius
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@LE.le.{0} Real Real.instLE
        (@Norm.norm.{0} Complex Complex.instNorm
          (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
            (Couret.STROBO2TORS.recohRationalComplexValue z) (Couret.STROBO2TORS.recohRationalComplexValue w)))
        (@Rat.cast.{0} Real Real.instRatCast radius)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_rational_ball_iff


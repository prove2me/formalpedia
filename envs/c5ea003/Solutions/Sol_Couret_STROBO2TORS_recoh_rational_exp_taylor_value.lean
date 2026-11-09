-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_rational_exp_taylor_value
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:44:29.81264+00:00
-- url     : https://prove2.me/submissions/ddbd50a8-f6e7-4554-94d0-361eccb8f049

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_complex_scale_value
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





















theorem recoh_rational_complex_mul_value (z w : RecohRationalComplex) :
    recohRationalComplexValue (recohRationalComplexMul z w) =
      recohRationalComplexValue z * recohRationalComplexValue w := by
  apply Complex.ext <;> simp [recohRationalComplexValue, recohRationalComplexMul]



theorem recoh_rational_complex_pow_value (z : RecohRationalComplex) (n : ℕ) :
    recohRationalComplexValue (recohRationalComplexPow z n) =
      (recohRationalComplexValue z) ^ n := by
  induction n with
  | zero => apply Complex.ext <;> simp [recohRationalComplexValue, recohRationalComplexPow]
  | succ n ih => rw [recohRationalComplexPow, recoh_rational_complex_mul_value, ih, pow_succ]



theorem p2m_local_recoh_rational_exp_taylor_value (t : ℚ) (n : ℕ) :
    recohRationalComplexValue (recohRationalExpTaylor t n) =
      ∑ k ∈ Finset.range n, (Complex.I * (t : ℂ)) ^ k / k.factorial := by
  change recohRationalComplexAddHom _ = _
  rw [recohRationalExpTaylor, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change recohRationalComplexValue _ = _
  rw [recoh_rational_complex_scale_value, recoh_rational_complex_pow_value]
  have ht : recohRationalComplexValue (0, t) = Complex.I * (t : ℂ) := by
    apply Complex.ext <;> simp [recohRationalComplexValue]
  rw [ht]
  push_cast
  ring













end Couret.STROBO2TORS


theorem solution : ∀ (t : Rat) (n : Nat),
  @Eq.{1} Complex (Couret.STROBO2TORS.recohRationalComplexValue (Couret.STROBO2TORS.recohRationalExpTaylor t n))
    (@Finset.sum.{0, 0} Nat Complex
      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
              (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Complex
                (@NormedCommRing.toNonUnitalNormedCommRing.{0} Complex
                  (@NormedField.toNormedCommRing.{0} Complex Complex.instNormedField)))))))
      (Finset.range n) fun k =>
      @HDiv.hDiv.{0, 0, 0} Complex Complex Complex
        (@instHDiv.{0} Complex (@DivInvMonoid.toDiv.{0} Complex Complex.instDivInvMonoid))
        (@HPow.hPow.{0, 0, 0} Complex Nat Complex
          (@instHPow.{0, 0} Complex Nat
            (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
          (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) Complex.I
            (@Rat.cast.{0} Complex Complex.instRatCast t))
          k)
        (@Nat.cast.{0} Complex Complex.instNatCast (Nat.factorial k))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_rational_exp_taylor_value


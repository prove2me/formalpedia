-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_newton_selected_probe_norm_of_square
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:54:34.093919+00:00
-- url     : https://prove2.me/submissions/f8437f8e-af7a-4be7-bf98-3cfe01884da3

import Definitions.Def_Couret_RecohTripleNewton_821bcf694d07
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_newton_selected_probe_norm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
Quantitative Newton identity for three unit complex numbers, and the
two-choice rational protocol used to replace a character by itself or its
cube before any support reading is measured.

The cube reading is the sum of the cubes of the three values. It is not the
cube of their sum. No distinctness of the values is assumed.

The rational comparison below is executable. Its correctness theorem takes
an explicit approximation certificate; this module does not construct that
certificate or establish extensionality for arbitrary approximation routines.
-/

namespace Couret.STROBO2TORS































/-- The same protocol accepts a certificate for the norm of the exact square
coefficient. The equality identifying that coefficient remains explicit. -/
theorem p2m_local_recoh_newton_selected_probe_norm_of_square (z₁ z₂ z₃ A : ℂ) (m : ℚ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1)
    (hA : A = (z₁ + z₂ + z₃) ^ 2)
    (hcert : |(m : ℝ) - ‖A‖| ≤ 1 / 8) :
    (1 / 2 : ℝ) ≤ ‖recohNewtonSelectedProbe z₁ z₂ z₃ m‖ := by
  apply recoh_newton_selected_probe_norm z₁ z₂ z₃ m h₁ h₂ h₃
  simpa only [hA, norm_pow] using hcert

end Couret.STROBO2TORS


theorem solution : ∀ (z₁ z₂ z₃ A : Complex) (m : Rat),
  @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm z₁)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
    @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm z₂)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm z₃)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @Eq.{1} Complex A
            (@HPow.hPow.{0, 0, 0} Complex Nat Complex
              (@instHPow.{0, 0} Complex Nat
                (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
              (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) z₁ z₂) z₃)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @LE.le.{0} Real Real.instLE
              (@abs.{0} Real Real.lattice Real.instAddGroup
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@Rat.cast.{0} Real Real.instRatCast m) (@Norm.norm.{0} Complex Complex.instNorm A)))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 8)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))) →
            @LE.le.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
              (@Norm.norm.{0} Complex Complex.instNorm (Couret.STROBO2TORS.recohNewtonSelectedProbe z₁ z₂ z₃ m)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_newton_selected_probe_norm_of_square


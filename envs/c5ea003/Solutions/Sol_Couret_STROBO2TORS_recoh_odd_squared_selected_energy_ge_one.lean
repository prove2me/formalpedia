-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_squared_selected_energy_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:42.353957+00:00
-- url     : https://prove2.me/submissions/45f02ac5-7bcb-4bec-ba3c-2fc40bfea859

import Definitions.Def_Couret_RecohOddPowerSelection_49cfa1cd1549
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_energy_dichotomy
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_squared_choice_energy_ge_one
import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

/-!
# Deterministic certified selection of an odd power

The executable search examines the rational approximations in ascending
index order, accepts the first value at least `3/2`, and falls back to index
zero.  Index `j` represents the odd character power `2*j+1`.

The contract uses an absolute error at most `1/2` on squared magnitude.
The root equations imply the dichotomy required to justify the fallback;
the selector never needs the hidden phases or an opposite-pair witness.
Constructing the rational approximations from a canonical square is a
separate obligation.  Extensionality below states the precise interface
that such a deterministic approximation procedure must satisfy.
-/

namespace Couret.STROBO2TORS













































/-- Applied squared-centre selection theorem for three roots of even
order.  The hidden phases occur only in the correctness statement. -/
theorem p2m_local_recoh_odd_squared_selected_energy_ge_one
    (m : ℕ) (hm : 0 < m) (a b c : ℂ)
    (ha : a ^ (2 * m) = 1) (hb : b ^ (2 * m) = 1)
    (hc : c ^ (2 * m) = 1) (actual centre : ℕ → ℂ) (sqNorm : ℕ → ℚ)
    (henergy : ∀ j < m, ‖actual j‖ = recohOddPowerEnergy a b c j)
    (hsq : ∀ j < m, (sqNorm j : ℝ) = ‖centre j‖ ^ 2)
    (herror : ∀ j < m, ‖centre j - actual j‖ ≤ (1 / 2 : ℝ)) :
    1 ≤ recohOddPowerEnergy a b c (recohOddSquaredChoice m sqNorm) := by
  apply recoh_odd_squared_choice_energy_ge_one m hm (recohOddPowerEnergy a b c)
    actual centre sqNorm henergy hsq herror
  rcases recoh_odd_power_energy_dichotomy m hm a b c ha hb hc with hall | hlarge
  · exact Or.inl (fun j _ => hall j)
  · exact Or.inr hlarge

end Couret.STROBO2TORS


theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀ (a b c : Complex),
      @Eq.{1} Complex
          (@HPow.hPow.{0, 0, 0} Complex Nat Complex
            (@instHPow.{0, 0} Complex Nat
              (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
            a
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
          (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
        @Eq.{1} Complex
            (@HPow.hPow.{0, 0, 0} Complex Nat Complex
              (@instHPow.{0, 0} Complex Nat
                (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
              b
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
            (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
          @Eq.{1} Complex
              (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                (@instHPow.{0, 0} Complex Nat
                  (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                c
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
            ∀ (actual centre : Nat → Complex) (sqNorm : Nat → Rat),
              (∀ (j : Nat),
                  @LT.lt.{0} Nat instLTNat j m →
                    @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm (actual j))
                      (Couret.STROBO2TORS.recohOddPowerEnergy a b c j)) →
                (∀ (j : Nat),
                    @LT.lt.{0} Nat instLTNat j m →
                      @Eq.{1} Real (@Rat.cast.{0} Real Real.instRatCast (sqNorm j))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid))
                          (@Norm.norm.{0} Complex Complex.instNorm (centre j))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  (∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j m →
                        @LE.le.{0} Real Real.instLE
                          (@Norm.norm.{0} Complex Complex.instNorm
                            (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                              (centre j) (actual j)))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (Couret.STROBO2TORS.recohOddPowerEnergy a b c (Couret.STROBO2TORS.recohOddSquaredChoice m sqNorm)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_squared_selected_energy_ge_one


-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_two_primary_odd_power_energy_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:29.988793+00:00
-- url     : https://prove2.me/submissions/30f36bdb-3ebf-4aff-8150-1c317b4b9e7e

import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_energy_dichotomy
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Averaging odd powers of three roots of even order

The order is written `2 * m`, with `0 < m`.  This includes the entire
2-primary case and keeps the geometric-sum argument independent of a
particular presentation of the order.  Repeated complex phases are allowed.

The energy at index `j` is the squared norm of the reading at exponent
`2 * j + 1`.  An opposite pair makes every such energy equal to one.
Otherwise their sum is at least `3 * m`, and some energy is at least three.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators









































/-- Specialization to order `2^(depth+1)`, matching binary-primary
character descriptors.  The search contains exactly `2^depth` odd powers. -/
theorem p2m_local_recoh_two_primary_odd_power_energy_dichotomy
    (depth : ℕ) (a b c : ℂ)
    (ha : a ^ (2 ^ (depth + 1)) = 1)
    (hb : b ^ (2 ^ (depth + 1)) = 1)
    (hc : c ^ (2 ^ (depth + 1)) = 1) :
    (∀ j : ℕ, recohOddPowerEnergy a b c j = 1) ∨
      ∃ j < 2 ^ depth, 3 ≤ recohOddPowerEnergy a b c j := by
  apply recoh_odd_power_energy_dichotomy (2 ^ depth) (by positivity) a b c
  · simpa [pow_succ, Nat.mul_comm] using ha
  · simpa [pow_succ, Nat.mul_comm] using hb
  · simpa [pow_succ, Nat.mul_comm] using hc

end Couret.STROBO2TORS


theorem solution : ∀ (depth : Nat) (a b c : Complex),
  @Eq.{1} Complex
      (@HPow.hPow.{0, 0, 0} Complex Nat Complex
        (@instHPow.{0, 0} Complex Nat (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
        a
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
    @Eq.{1} Complex
        (@HPow.hPow.{0, 0, 0} Complex Nat Complex
          (@instHPow.{0, 0} Complex Nat
            (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
          b
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
      @Eq.{1} Complex
          (@HPow.hPow.{0, 0, 0} Complex Nat Complex
            (@instHPow.{0, 0} Complex Nat
              (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
            c
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
        Or
          (∀ (j : Nat),
            @Eq.{1} Real (Couret.STROBO2TORS.recohOddPowerEnergy a b c j)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@Exists.{1} Nat fun j =>
            And
              (@LT.lt.{0} Nat instLTNat j
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) depth))
              (@LE.le.{0} Real Real.instLE
                (@OfNat.ofNat.{0} Real (nat_lit 3)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                (Couret.STROBO2TORS.recohOddPowerEnergy a b c j))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_two_primary_odd_power_energy_dichotomy


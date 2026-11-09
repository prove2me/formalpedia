-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_power_energy_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:04:02.659012+00:00
-- url     : https://prove2.me/submissions/b0e630a2-a463-43f8-a98e-b1394780c6af

import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_energy_eq_one_of_opposite
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_energy_sum_ge
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





































/-- A nonempty finite family with mean at least three has a member at
least three.  This is the exact finite averaging step used below. -/
theorem recoh_exists_energy_ge_three (m : ℕ) (hm : 0 < m) (energy : ℕ → ℝ)
    (hsum : 3 * (m : ℝ) ≤ ∑ j ∈ Finset.range m, energy j) :
    ∃ j < m, 3 ≤ energy j := by
  by_contra! h
  have hlt : (∑ j ∈ Finset.range m, energy j) < ∑ _j ∈ Finset.range m, (3 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact le_of_lt (h j (Finset.mem_range.mp hj))
    · exact ⟨0, Finset.mem_range.mpr hm, h 0 hm⟩
  have hconst : (∑ _j ∈ Finset.range m, (3 : ℝ)) = 3 * (m : ℝ) := by simp; ring
  linarith

/-- The root equations themselves imply the dichotomy needed by the
certified rational selector: all energies are one, or some is at least three. -/
theorem p2m_local_recoh_odd_power_energy_dichotomy (m : ℕ) (hm : 0 < m) (a b c : ℂ)
    (ha : a ^ (2 * m) = 1) (hb : b ^ (2 * m) = 1)
    (hc : c ^ (2 * m) = 1) :
    (∀ j : ℕ, recohOddPowerEnergy a b c j = 1) ∨
      ∃ j < m, 3 ≤ recohOddPowerEnergy a b c j := by
  by_cases hop : RecohHasOppositePair a b c
  · left
    have horder : 2 * m ≠ 0 := by omega
    exact recoh_odd_power_energy_eq_one_of_opposite a b c
      (Complex.norm_eq_one_of_pow_eq_one ha horder)
      (Complex.norm_eq_one_of_pow_eq_one hb horder)
      (Complex.norm_eq_one_of_pow_eq_one hc horder) hop
  · right
    exact recoh_exists_energy_ge_three m hm (recohOddPowerEnergy a b c)
      (recoh_odd_power_energy_sum_ge m hm a b c ha hb hc hop)



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
            Or
              (∀ (j : Nat),
                @Eq.{1} Real (Couret.STROBO2TORS.recohOddPowerEnergy a b c j)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              (@Exists.{1} Nat fun j =>
                And (@LT.lt.{0} Nat instLTNat j m)
                  (@LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 3)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                    (Couret.STROBO2TORS.recohOddPowerEnergy a b c j))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_power_energy_dichotomy


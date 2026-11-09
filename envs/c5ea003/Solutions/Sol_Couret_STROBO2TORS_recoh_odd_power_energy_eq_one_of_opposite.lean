-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_power_energy_eq_one_of_opposite
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:38.583196+00:00
-- url     : https://prove2.me/submissions/e2e1ff39-407b-47f8-a0ed-2beb7751e9fd

import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
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



































/-- An opposite pair cancels at every odd exponent, leaving energy one. -/
theorem p2m_local_recoh_odd_power_energy_eq_one_of_opposite (a b c : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hop : RecohHasOppositePair a b c) (j : ℕ) :
    recohOddPowerEnergy a b c j = 1 := by
  have hneg (z : ℂ) : (-z) ^ (2 * j + 1) = -(z ^ (2 * j + 1)) := by
    rw [neg_pow]
    have hone : (-1 : ℂ) ^ (2 * j + 1) = -1 := by simp [pow_add, pow_mul]
    rw [hone, neg_one_mul]
  rcases hop with hab | hac | hbc
  · rw [recohOddPowerEnergy, hab, hneg]
    simp [norm_pow, hc]
  · rw [recohOddPowerEnergy, hac, hneg]
    have hcancel : -(c ^ (2 * j + 1)) + b ^ (2 * j + 1) + c ^ (2 * j + 1) =
        b ^ (2 * j + 1) := by ring
    rw [hcancel]
    simp [norm_pow, hb]
  · rw [recohOddPowerEnergy, hbc, hneg]
    have hcancel : a ^ (2 * j + 1) + -(c ^ (2 * j + 1)) + c ^ (2 * j + 1) =
        a ^ (2 * j + 1) := by ring
    rw [hcancel]
    simp [norm_pow, ha]







end Couret.STROBO2TORS


theorem solution : ∀ (a b c : Complex),
  @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm a)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
    @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm b)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm c)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        Couret.STROBO2TORS.RecohHasOppositePair a b c →
          ∀ (j : Nat),
            @Eq.{1} Real (Couret.STROBO2TORS.recohOddPowerEnergy a b c j)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_power_energy_eq_one_of_opposite


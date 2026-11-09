-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_power_choice_energy_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:54:37.645195+00:00
-- url     : https://prove2.me/submissions/33eeb3e7-f6c9-4d08-8a1d-60b9b48da5a7

import Definitions.Def_Couret_RecohOddPowerSelection_49cfa1cd1549
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_find_none
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_find_some
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



















/-- The rational protocol has a unit energy guarantee for the exact
dichotomy established by odd-power averaging. -/
theorem p2m_local_recoh_odd_power_choice_energy_ge_one
    (m : ℕ) (hm : 0 < m) (energy : ℕ → ℝ) (approx : ℕ → ℚ)
    (hcert : ∀ j < m, |(approx j : ℝ) - energy j| ≤ (1 / 2 : ℝ))
    (hdich : (∀ j < m, energy j = 1) ∨ ∃ j < m, 3 ≤ energy j) :
    1 ≤ energy (recohOddPowerChoice m approx) := by
  cases hfind : recohOddPowerFind approx (List.range m) with
  | none =>
      have hfailed := recoh_odd_power_find_none approx (List.range m) hfind
      rcases hdich with hall | ⟨j, hj, hlarge⟩
      · simp [recohOddPowerChoice, hfind, hall 0 hm]
      · have hbad : approx j < (3 / 2 : ℚ) := hfailed j (List.mem_range.mpr hj)
        have hbadreal : (approx j : ℝ) < (3 / 2 : ℝ) := by
          simpa only [Rat.cast_div, Rat.cast_ofNat] using
            (Rat.cast_lt (K := ℝ)).mpr hbad
        have herror := (abs_le.mp (hcert j hj)).1
        exfalso
        linarith
  | some j =>
      obtain ⟨hmem, hgood⟩ := recoh_odd_power_find_some approx (List.range m) j hfind
      have hj : j < m := List.mem_range.mp hmem
      have hgoodreal : (3 / 2 : ℝ) ≤ (approx j : ℝ) := by
        simpa only [Rat.cast_div, Rat.cast_ofNat] using
          (Rat.cast_le (K := ℝ)).mpr hgood
      have herror := (abs_le.mp (hcert j hj)).2
      have henergy : 1 ≤ energy j := by linarith
      simpa [recohOddPowerChoice, hfind] using henergy



























end Couret.STROBO2TORS


theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀ (energy : Nat → Real) (approx : Nat → Rat),
      (∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j m →
            @LE.le.{0} Real Real.instLE
              (@abs.{0} Real Real.lattice Real.instAddGroup
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@Rat.cast.{0} Real Real.instRatCast (approx j)) (energy j)))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
        Or
            (∀ (j : Nat),
              @LT.lt.{0} Nat instLTNat j m →
                @Eq.{1} Real (energy j) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            (@Exists.{1} Nat fun j =>
              And (@LT.lt.{0} Nat instLTNat j m)
                (@LE.le.{0} Real Real.instLE
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  (energy j))) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (energy (Couret.STROBO2TORS.recohOddPowerChoice m approx)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_power_choice_energy_ge_one


-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_power_find_none
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:51:45.549059+00:00
-- url     : https://prove2.me/submissions/2640f2b1-94c3-469c-aa60-4a255791843a

import Definitions.Def_Couret_RecohOddPowerSelection_49cfa1cd1549
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
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









/-- A failed search certifies that every inspected rational missed the threshold. -/
theorem p2m_local_recoh_odd_power_find_none (approx : ℕ → ℚ) (js : List ℕ) :
    recohOddPowerFind approx js = none →
      ∀ j ∈ js, approx j < (3 / 2 : ℚ) := by
  induction js with
  | nil => simp
  | cons i is ih =>
      intro h j hj
      by_cases hgood : (3 / 2 : ℚ) ≤ approx i
      · simp [recohOddPowerFind, hgood] at h
      · have htail : recohOddPowerFind approx is = none := by
          simpa only [recohOddPowerFind, hgood, if_false] using h
        rcases List.mem_cons.mp hj with hji | hmem
        · subst j
          exact lt_of_not_ge hgood
        · exact ih htail j hmem





































end Couret.STROBO2TORS


theorem solution : ∀ (approx : Nat → Rat) (js : List.{0} Nat),
  @Eq.{1} (Option.{0} Nat) (Couret.STROBO2TORS.recohOddPowerFind approx js) (@Option.none.{0} Nat) →
    ∀ (j : Nat),
      @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) js j →
        @LT.lt.{0} Rat Rat.instLT (approx j)
          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3)))
            (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_power_find_none


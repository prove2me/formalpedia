-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_predicate_choice_spec
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:48.339716+00:00
-- url     : https://prove2.me/submissions/c13a807f-d244-4959-8885-3e9719922d30

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





























/-- The chosen index passes the test, or all candidates failed and the
explicit canonical fallback is index zero. -/
theorem p2m_local_recoh_odd_predicate_choice_spec (m : ℕ) (accept : ℕ → Bool) :
    accept (recohOddPredicateChoice m accept) = true ∨
      (recohOddPredicateChoice m accept = 0 ∧ ∀ j < m, accept j = false) := by
  let approx : ℕ → ℚ := fun j => if accept j then 2 else 0
  change accept (recohOddPowerChoice m approx) = true ∨
    (recohOddPowerChoice m approx = 0 ∧ ∀ j < m, accept j = false)
  cases hfind : recohOddPowerFind approx (List.range m) with
  | none =>
      right
      constructor
      · simp [recohOddPowerChoice, hfind]
      · intro j hj
        have hbad := recoh_odd_power_find_none approx (List.range m) hfind j
          (List.mem_range.mpr hj)
        cases hb : accept j
        · rfl
        · norm_num [approx, hb] at hbad
  | some j =>
      left
      have hgood := (recoh_odd_power_find_some approx (List.range m) j hfind).2
      have haccept : accept j = true := by
        cases hb : accept j
        · norm_num [approx, hb] at hgood
        · rfl
      simpa [recohOddPowerChoice, hfind] using haccept

















end Couret.STROBO2TORS


theorem solution : ∀ (m : Nat) (accept : Nat → Bool),
  Or (@Eq.{1} Bool (accept (Couret.STROBO2TORS.recohOddPredicateChoice m accept)) Bool.true)
    (And
      (@Eq.{1} Nat (Couret.STROBO2TORS.recohOddPredicateChoice m accept)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (∀ (j : Nat), @LT.lt.{0} Nat instLTNat j m → @Eq.{1} Bool (accept j) Bool.false)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_predicate_choice_spec


-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_power_find_some
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:51:50.45389+00:00
-- url     : https://prove2.me/submissions/9c7f9678-19db-48f0-a076-1b6033f4a5a2

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







/-- Every successful search result was present and met the rational threshold. -/
theorem p2m_local_recoh_odd_power_find_some (approx : ℕ → ℚ) (js : List ℕ) (j : ℕ) :
    recohOddPowerFind approx js = some j →
      j ∈ js ∧ (3 / 2 : ℚ) ≤ approx j := by
  induction js with
  | nil => simp [recohOddPowerFind]
  | cons i is ih =>
      intro h
      by_cases hgood : (3 / 2 : ℚ) ≤ approx i
      · simp only [recohOddPowerFind, hgood, if_true, Option.some.injEq] at h
        subst j
        exact ⟨by simp, hgood⟩
      · have htail : recohOddPowerFind approx is = some j := by
          simpa only [recohOddPowerFind, hgood, if_false] using h
        obtain ⟨hmem, hj⟩ := ih htail
        exact ⟨List.mem_cons_of_mem i hmem, hj⟩







































end Couret.STROBO2TORS


theorem solution : ∀ (approx : Nat → Rat) (js : List.{0} Nat) (j : Nat),
  @Eq.{1} (Option.{0} Nat) (Couret.STROBO2TORS.recohOddPowerFind approx js) (@Option.some.{0} Nat j) →
    And (@Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) js j)
      (@LE.le.{0} Rat Rat.instLE
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))))
        (approx j)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_power_find_some


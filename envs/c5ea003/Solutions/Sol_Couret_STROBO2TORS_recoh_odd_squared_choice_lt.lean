-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_squared_choice_lt
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:54:39.438964+00:00
-- url     : https://prove2.me/submissions/9d1d686a-742c-47c9-a706-509f962d7526

import Definitions.Def_Couret_RecohOddPowerSelection_49cfa1cd1549
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
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













/-- The selected index is valid, including the explicit fallback, when `m>0`. -/
theorem recoh_odd_power_choice_lt (m : ℕ) (hm : 0 < m) (approx : ℕ → ℚ) :
    recohOddPowerChoice m approx < m := by
  cases hfind : recohOddPowerFind approx (List.range m) with
  | none => simpa [recohOddPowerChoice, hfind] using hm
  | some j =>
      have hj := (recoh_odd_power_find_some approx (List.range m) j hfind).1
      simpa [recohOddPowerChoice, hfind] using (List.mem_range.mp hj)













/-- A Boolean-test choice stays in the odd-power index range. -/
theorem recoh_odd_predicate_choice_lt (m : ℕ) (hm : 0 < m) (accept : ℕ → Bool) :
    recohOddPredicateChoice m accept < m :=
  recoh_odd_power_choice_lt m hm _











/-- A squared-centre selection remains inside the finite index range. -/
theorem p2m_local_recoh_odd_squared_choice_lt (m : ℕ) (hm : 0 < m) (sqNorm : ℕ → ℚ) :
    recohOddSquaredChoice m sqNorm < m :=
  recoh_odd_predicate_choice_lt m hm _







end Couret.STROBO2TORS


theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀ (sqNorm : Nat → Rat), @LT.lt.{0} Nat instLTNat (Couret.STROBO2TORS.recohOddSquaredChoice m sqNorm) m := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_squared_choice_lt


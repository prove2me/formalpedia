-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_squared_choice_eq_fast
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:54:45.376354+00:00
-- url     : https://prove2.me/submissions/d1438b17-1b4d-4611-874d-36814df4bcf7

import Definitions.Def_Couret_RecohOddPowerRuntime_8c8d44664d18
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_Couret_RecohOddPowerSelection_49cfa1cd1549

set_option autoImplicit false

/-!
# Certified short-circuit execution of the odd-power selector

The mathematical selector is specified using `List.range`.  Constructing
that list before searching would allocate the whole search interval even
when its first index succeeds.  The implementation below instead carries
the current index and the remaining number of candidates.  Its recursive
call is reached only after the current candidate fails.

The equivalence with the list specification is proved for every start
and count.  Compiler simplification also replaces the public wrappers,
which were compiled before this module introduced the replacement.
The search order, inclusive thresholds, and zero fallback are unchanged.
-/

namespace Couret.STROBO2TORS



/-- The counter-based search has exactly the list specification's result. -/
theorem recoh_odd_power_find_from_eq (approx : ℕ → ℚ) (start count : ℕ) :
    recohOddPowerFindFrom approx start count =
      recohOddPowerFind approx (List.range' start count) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [recohOddPowerFindFrom, List.range'_succ, recohOddPowerFind, ih]



/-- Replace the list allocation by the proved-equivalent short-circuit search. -/
@[csimp] theorem recoh_odd_power_choice_eq_fast :
    @recohOddPowerChoice = @recohOddPowerChoiceFast := by
  funext m approx
  simp only [recohOddPowerChoice, recohOddPowerChoiceFast,
    recoh_odd_power_find_from_eq, List.range_eq_range']







@[csimp] theorem recoh_odd_predicate_choice_eq_fast :
    @recohOddPredicateChoice = @recohOddPredicateChoiceFast := by
  funext m accept
  simp only [recohOddPredicateChoice, recohOddPredicateChoiceFast,
    recoh_odd_power_choice_eq_fast]



@[csimp] theorem p2m_local_recoh_odd_squared_choice_eq_fast :
    @recohOddSquaredChoice = @recohOddSquaredChoiceFast := by
  funext m sqNorm
  simp only [recohOddSquaredChoice, recohOddSquaredChoiceFast,
    recoh_odd_predicate_choice_eq_fast]

end Couret.STROBO2TORS


theorem solution : @Eq.{1} (Nat → (Nat → Rat) → Nat) Couret.STROBO2TORS.recohOddSquaredChoice Couret.STROBO2TORS.recohOddSquaredChoiceFast := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_squared_choice_eq_fast


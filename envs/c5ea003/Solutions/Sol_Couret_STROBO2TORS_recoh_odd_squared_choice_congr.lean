-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_squared_choice_congr
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:54:38.530439+00:00
-- url     : https://prove2.me/submissions/506b2f4a-27b5-4d89-85d0-39055ec95918

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











/-- Equal approximations on the inspected list give exactly the same search result. -/
theorem recoh_odd_power_find_congr (approx other : ℕ → ℚ) (js : List ℕ)
    (heq : ∀ j ∈ js, approx j = other j) :
    recohOddPowerFind approx js = recohOddPowerFind other js := by
  induction js with
  | nil => rfl
  | cons i is ih =>
      have hi : approx i = other i := heq i (by simp)
      have htail : ∀ j ∈ is, approx j = other j := by
        intro j hj
        exact heq j (List.mem_cons_of_mem i hj)
      simp only [recohOddPowerFind, hi, ih htail]





/-- Extensionality requires equality of the canonical approximation outputs,
not merely two valid error certificates. -/
theorem recoh_odd_power_choice_congr (m : ℕ) (approx other : ℕ → ℚ)
    (heq : ∀ j < m, approx j = other j) :
    recohOddPowerChoice m approx = recohOddPowerChoice m other := by
  unfold recohOddPowerChoice
  rw [recoh_odd_power_find_congr approx other (List.range m)
    (fun j hj => heq j (List.mem_range.mp hj))]













/-- The deterministic Boolean selection depends only on the tested values
in the finite candidate range. -/
theorem recoh_odd_predicate_choice_congr (m : ℕ) (accept other : ℕ → Bool)
    (heq : ∀ j < m, accept j = other j) :
    recohOddPredicateChoice m accept = recohOddPredicateChoice m other := by
  apply recoh_odd_power_choice_congr
  intro j hj
  rw [heq j hj]









/-- Determinism of the squared-centre selector on the finite candidate range. -/
theorem p2m_local_recoh_odd_squared_choice_congr (m : ℕ) (sqNorm other : ℕ → ℚ)
    (heq : ∀ j < m, sqNorm j = other j) :
    recohOddSquaredChoice m sqNorm = recohOddSquaredChoice m other := by
  apply recoh_odd_predicate_choice_congr
  intro j hj
  rw [heq j hj]





end Couret.STROBO2TORS


theorem solution : ∀ (m : Nat) (sqNorm other : Nat → Rat),
  (∀ (j : Nat), @LT.lt.{0} Nat instLTNat j m → @Eq.{1} Rat (sqNorm j) (other j)) →
    @Eq.{1} Nat (Couret.STROBO2TORS.recohOddSquaredChoice m sqNorm) (Couret.STROBO2TORS.recohOddSquaredChoice m other) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_squared_choice_congr


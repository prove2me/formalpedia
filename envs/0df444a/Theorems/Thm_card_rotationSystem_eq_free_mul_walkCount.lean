-- Prove2me | Theorems.Thm_card_rotationSystem_eq_free_mul_walkCount
-- name    : card_rotationSystem_eq_free_mul_walkCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:00.902058+00:00
-- url     : https://prove2.me/theorems/d95dca43-56ca-5338-965a-c5a5d1d4b8f0
-- title:
--   card rotation System eq free mul walk Count: card rotation System eq free mul walk Count
-- statement:
--   The card rotation System eq free mul walk Count construction uses the card rotation System eq free mul walk Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3789-L3798
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3789-L3798

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]

theorem card_rotationSystem_eq_free_mul_walkCount
    (d : ℕ) [NeZero d] (G : SimpleGraph V)
    (hG : IsRegularOfDegree G d) (start : OrientedEdge G)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k < Fintype.card V) :
    Nat.card (RotationSystem d V) =
      (d - 1) ^ (Fintype.card V - (k - 1)) * walkCount G start k := by sorry

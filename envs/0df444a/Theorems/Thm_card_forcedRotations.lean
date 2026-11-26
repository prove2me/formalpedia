-- Prove2me | Theorems.Thm_card_forcedRotations
-- name    : card_forcedRotations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:02.024878+00:00
-- url     : https://prove2.me/theorems/ccf4079a-b43f-5bf9-a045-5ba771c855b8
-- title:
--   card forced Rotations: card forced Rotations
-- statement:
--   The card forced Rotations construction uses the card forced Rotations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L522-L526
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L522-L526

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
noncomputable section
variable {V : Type*} [Fintype V]
variable (d : ℕ) [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] graphAdjDecidable
attribute [local instance] vertexDecidableEq
variable {m : ℕ} (start : OrientedEdge G)

theorem card_forcedRotations (w : SimpleNonbacktrackingWalk G start (m + 1)) :
    Nat.card (ForcedRotations d G hG start w) =
      (d - 1) ^ (Fintype.card V - m) := by sorry

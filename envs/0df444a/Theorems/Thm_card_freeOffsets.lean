-- Prove2me | Theorems.Thm_card_freeOffsets
-- name    : card_freeOffsets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:59.648718+00:00
-- url     : https://prove2.me/theorems/8c5ce179-c6e8-517c-b0f5-cce9c7ac0c7d
-- title:
--   card free Offsets: card free Offsets
-- statement:
--   The card free Offsets construction uses the card free Offsets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L509-L520
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L509-L520

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

theorem card_freeOffsets (w : SimpleNonbacktrackingWalk G start (m + 1)) :
    Nat.card (FreeOffsets d G start w) =
      (d - 1) ^ (Fintype.card V - m) := by sorry

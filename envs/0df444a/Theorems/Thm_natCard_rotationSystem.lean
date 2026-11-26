-- Prove2me | Theorems.Thm_natCard_rotationSystem
-- name    : natCard_rotationSystem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:50.983826+00:00
-- url     : https://prove2.me/theorems/4858584b-923a-4f1d-bc94-f854dbbded82
-- title:
--   nat Card rotation System: nat Card rotation System
-- statement:
--   The nat Card rotation System construction uses the nat Card rotation System property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3769-L3771
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3769-L3771

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

theorem natCard_rotationSystem (d : ℕ) [NeZero d] :
  Nat.card (RotationSystem d V) = (d - 1) ^ Fintype.card V := by sorry

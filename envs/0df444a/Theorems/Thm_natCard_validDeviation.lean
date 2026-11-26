-- Prove2me | Theorems.Thm_natCard_validDeviation
-- name    : natCard_validDeviation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:15.245217+00:00
-- url     : https://prove2.me/theorems/290a27b6-46d5-55f1-addb-02744e64bd79
-- title:
--   nat Card valid Deviation: nat Card valid Deviation
-- statement:
--   The nat Card valid Deviation construction uses the nat Card valid Deviation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L663-L669
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L663-L669

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

theorem natCard_validDeviation (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) :
    Nat.card (ValidDeviation d G hG start rho k) = (k - 1) * (d - 2) := by sorry

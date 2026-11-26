-- Prove2me | Theorems.Thm_natCard_exceptionalDeviation_le
-- name    : natCard_exceptionalDeviation_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:47.342468+00:00
-- url     : https://prove2.me/theorems/2d9398be-ca8a-49f9-83c8-b53243a5d0c9
-- title:
--   nat Card exceptional Deviation le: nat Card exceptional Deviation le
-- statement:
--   The nat Card exceptional Deviation le construction uses the nat Card exceptional Deviation le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1113-L1118
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1113-L1118

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

theorem natCard_exceptionalDeviation_le (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Nat.card (ExceptionalDeviation d G hG start rho) ≤ 4 * d := by sorry

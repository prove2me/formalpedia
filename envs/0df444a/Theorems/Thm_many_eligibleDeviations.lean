-- Prove2me | Theorems.Thm_many_eligibleDeviations
-- name    : many_eligibleDeviations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:28.222389+00:00
-- url     : https://prove2.me/theorems/43f5e665-9b9a-45f3-8d52-b4731d29beee
-- title:
--   many eligible Deviations: many eligible Deviations
-- statement:
--   In the high regime, every good plan has linearly many classified short
--   returns, even though we only retain a degree-independent `k/4` lower bound.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1738-L1817
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1738-L1817

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

theorem many_eligibleDeviations (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (hd : 3 ≤ d)
    (hhigh : 1048576 * d ^ 2 * Fintype.card V ≤ k ^ 2)
    (hkn : k < Fintype.card V) :
    k ≤ 4 * (eligibleDeviations d G hG start rho).card := by sorry

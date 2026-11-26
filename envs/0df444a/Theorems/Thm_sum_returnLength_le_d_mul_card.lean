-- Prove2me | Theorems.Thm_sum_returnLength_le_d_mul_card
-- name    : sum_returnLength_le_d_mul_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:12.558892+00:00
-- url     : https://prove2.me/theorems/b4170cc0-59d2-53e8-8e4f-8f754cfddb0c
-- title:
--   sum return Length le d mul card: sum return Length le d mul card
-- statement:
--   The sum return Length le d mul card construction uses the sum return Length le d mul card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1705-L1720
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1705-L1720

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

theorem sum_returnLength_le_d_mul_card (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    ∑ q : ValidDeviation d G hG start rho.1 k,
      returnLength d G hG start rho.1 k q ≤ d * Fintype.card V := by sorry

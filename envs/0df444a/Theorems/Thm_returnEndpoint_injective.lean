-- Prove2me | Theorems.Thm_returnEndpoint_injective
-- name    : returnEndpoint_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:46.793356+00:00
-- url     : https://prove2.me/theorems/e0e581ee-dedf-4231-90f6-ba57e2edd3ef
-- title:
--   return Endpoint injective: return Endpoint injective
-- statement:
--   The return Endpoint injective construction uses the return Endpoint injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1013-L1019
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1013-L1019

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

theorem returnEndpoint_injective (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Function.Injective (returnEndpoint d G hG start rho.1 k) := by sorry

-- Prove2me | Theorems.Thm_exceptionalDeviationToDart_injective
-- name    : exceptionalDeviationToDart_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:40.987833+00:00
-- url     : https://prove2.me/theorems/24963c80-ae63-414b-b3db-4dbd272cf70b
-- title:
--   exceptional Deviation To Dart injective: exceptional Deviation To Dart injective
-- statement:
--   The exceptional Deviation To Dart injective construction uses the exceptional Deviation To Dart injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1104-L1111
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1104-L1111

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

theorem exceptionalDeviationToDart_injective (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Function.Injective (exceptionalDeviationToDart d G hG start rho) := by sorry

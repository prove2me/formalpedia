-- Prove2me | Theorems.Thm_finishDeviation_injective_off_exceptional
-- name    : finishDeviation_injective_off_exceptional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:48.831803+00:00
-- url     : https://prove2.me/theorems/a78a058f-c8f0-58fe-b167-127e56d911ce
-- title:
--   finish Deviation injective off exceptional: finish Deviation injective off exceptional
-- statement:
--   The finish Deviation injective off exceptional construction uses the finish Deviation injective off exceptional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1487-L1500
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1487-L1500

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

theorem finishDeviation_injective_off_exceptional (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Set.InjOn (finishDeviation d G hG start rho)
      ((Finset.univ \ exceptionalDeviations d G hG start rho :
        Finset (ValidDeviation d G hG start rho.1 k)) :
          Set (ValidDeviation d G hG start rho.1 k)) := by sorry

-- Prove2me | Theorems.Thm_card_startBoundary_le
-- name    : card_startBoundary_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:16.698079+00:00
-- url     : https://prove2.me/theorems/9551713d-0797-4c05-a054-a0af2201e557
-- title:
--   card start Boundary le: card start Boundary le
-- statement:
--   The card start Boundary le construction uses the card start Boundary le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1681-L1689
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1681-L1689

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

theorem card_startBoundary_le (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) (L : ℕ) :
    (DegreeEligibleArithmetic.boundaryBad Finset.univ
      (deviationStartTime d G hG start rho) k L).card ≤ L * d := by sorry

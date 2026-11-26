-- Prove2me | Theorems.Thm_card_finishBoundary_le
-- name    : card_finishBoundary_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:08.740917+00:00
-- url     : https://prove2.me/theorems/7dbd00a4-7a76-5ef1-b5a5-2134af5746ab
-- title:
--   card finish Boundary le: card finish Boundary le
-- statement:
--   The card finish Boundary le construction uses the card finish Boundary le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1691-L1703
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1691-L1703

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

theorem card_finishBoundary_le (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) (L : ℕ) :
    (DegreeEligibleArithmetic.boundaryBad
      (Finset.univ \ exceptionalDeviations d G hG start rho)
      (deviationFinishTime d G hG start rho) k L).card ≤ L * d := by sorry

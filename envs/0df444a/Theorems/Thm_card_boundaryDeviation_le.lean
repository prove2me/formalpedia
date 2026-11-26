-- Prove2me | Theorems.Thm_card_boundaryDeviation_le
-- name    : card_boundaryDeviation_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:43.135826+00:00
-- url     : https://prove2.me/theorems/d63316c9-3974-54bc-848c-ccedde120ec6
-- title:
--   card boundary Deviation le: card boundary Deviation le
-- statement:
--   A boundary strip has at most `L` possible path indices and at most
--   `d-1` possible offset labels.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1627-L1679
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1627-L1679

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

theorem card_boundaryDeviation_le (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (J : Finset (ValidDeviation d G hG start rho.1 k))
    (f : ValidDeviation d G hG start rho.1 k →
      ValidDeviation d G hG start rho.1 k)
    (hf : Set.InjOn f (J : Set (ValidDeviation d G hG start rho.1 k)))
    (L : ℕ) :
    (DegreeEligibleArithmetic.boundaryBad J
      (fun q ↦ internalTime (f q).1.1) k L).card ≤ L * d := by sorry

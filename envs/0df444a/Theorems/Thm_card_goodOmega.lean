-- Prove2me | Theorems.Thm_card_goodOmega
-- name    : card_goodOmega
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:57.165961+00:00
-- url     : https://prove2.me/theorems/65edaf06-ddb4-5f6a-ba49-35dedfbd72dc
-- title:
--   card good Omega: card good Omega
-- statement:
--   The card good Omega construction uses the card good Omega property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3773-L3781
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3773-L3781

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
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]

theorem card_goodOmega (d : ℕ) [NeZero d] (G : SimpleGraph V)
    (hG : IsRegularOfDegree G d) (start : OrientedEdge G)
    (k : ℕ) (hk : 1 ≤ k) :
    Nat.card (GoodOmega d G hG start k) =
      simpleWalkCount G start k *
        (d - 1) ^ (Fintype.card V - (k - 1)) := by sorry

-- Prove2me | Theorems.Thm_birthday_paradox
-- name    : birthday_paradox
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:11:17.355319+00:00
-- url     : https://prove2.me/theorems/6fa06aa5-eb16-5947-9a41-eca280eb1bff
-- title:
--   birthday paradox: birthday paradox
-- statement:
--   The birthday paradox construction uses the birthday paradox property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L4139-L4154
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L4139-L4154

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
universe u

theorem birthday_paradox
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        IsRegularOfDegree G d →
        ∀ (k : ℕ) (start : OrientedEdge G),
          C * Real.sqrt (Fintype.card V : ℝ) < (k : ℝ) →
            simpleProbability G start k < ε := by sorry

-- Prove2me | Theorems.Thm_simpleProbability_eq_goodRatio
-- name    : simpleProbability_eq_goodRatio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:23.303808+00:00
-- url     : https://prove2.me/theorems/bc54b816-ab25-451e-b9b3-09a37959d485
-- title:
--   simple Probability eq good Ratio: simple Probability eq good Ratio
-- statement:
--   The simple Probability eq good Ratio construction uses the simple Probability eq good Ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3800-L3821
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L3800-L3821

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

theorem simpleProbability_eq_goodRatio
    (d : ℕ) [NeZero d] (hd : 3 ≤ d) (G : SimpleGraph V)
    (hG : IsRegularOfDegree G d) (start : OrientedEdge G)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k < Fintype.card V) :
    simpleProbability G start k =
      (Nat.card (GoodOmega d G hG start k) : ℝ) /
        (Nat.card (RotationSystem d V) : ℝ) := by sorry

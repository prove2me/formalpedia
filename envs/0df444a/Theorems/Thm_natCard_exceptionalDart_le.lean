-- Prove2me | Theorems.Thm_natCard_exceptionalDart_le
-- name    : natCard_exceptionalDart_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:31.347216+00:00
-- url     : https://prove2.me/theorems/26dcf1c5-43b2-5a13-a038-fa25820ccc6a
-- title:
--   nat Card exceptional Dart le: nat Card exceptional Dart le
-- statement:
--   The nat Card exceptional Dart le construction uses the nat Card exceptional Dart le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1080-L1090
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1080-L1090

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

theorem natCard_exceptionalDart_le (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ) :
    Nat.card (ExceptionalDart d G hG start rho k) ≤ 4 * d := by sorry

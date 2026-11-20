-- Prove2me | Theorems.Thm_exists_av_and_ex_eq
-- name    : exists_av_and_ex_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:02:19.649521+00:00
-- url     : https://prove2.me/theorems/7aeec9e0-6ee0-40cc-b872-191d6c5fc492
-- title:
--   exists av and ex eq: exists av and ex eq
-- statement:
--   The exists av and ex eq construction uses the exists av and ex eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L198-L202
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L198-L202

module
public import Definitions.Def_ScoutForbiddenMatrixContainment
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Definitions.Def_ForbiddenMatrix_ExtremalFunction
set_option autoImplicit true
@[expose] public section
public section
open Finset
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ] {m n : ℕ}
  {P : α → β → Prop}

theorem exists_av_and_ex_eq {n : ℕ} {P : α → β → Prop} (P_nonempty : ∃ a b, P a b) :
    ∃ M : Fin n → Fin n → Prop, ¬ Contains P M ∧ ex P n = density M := by sorry

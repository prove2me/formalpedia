-- Prove2me | Theorems.Thm_not_contains_false
-- name    : not_contains_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:14:17.237437+00:00
-- url     : https://prove2.me/theorems/69516125-60b1-48b7-9696-af954e1f5937
-- title:
--   not contains false: not contains false
-- statement:
--   The not contains false construction uses the not contains false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/Containment.lean#L30-L31
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/Containment.lean#L30-L31

module
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_ScoutForbiddenMatrixContainment
set_option autoImplicit true
@[expose] public section
public section
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]
  {P : α → β → Prop} {M : γ → δ → Prop}

theorem not_contains_false (P : α → β → Prop) (P_nonempty : ∃ a b, P a b) :
    ¬ Contains P fun (_ : γ) (_ : δ) ↦ False := by sorry

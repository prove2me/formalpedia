-- Prove2me | Theorems.Thm_contains_refl
-- name    : contains_refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:12:42.99091+00:00
-- url     : https://prove2.me/theorems/c808bcfd-c65f-4891-a32c-ede079d10514
-- title:
--   contains refl: contains refl
-- statement:
--   The contains refl construction uses the contains refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/Containment.lean#L22-L23
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/Containment.lean#L22-L23

module
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_ScoutForbiddenMatrixContainment
set_option autoImplicit true
@[expose] public section
public section
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]
  {P : α → β → Prop} {M : γ → δ → Prop}

theorem contains_refl (M : γ → δ → Prop) : Contains M M := by sorry

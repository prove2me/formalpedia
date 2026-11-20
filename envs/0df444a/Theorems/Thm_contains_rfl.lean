-- Prove2me | Theorems.Thm_contains_rfl
-- name    : contains_rfl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:13:32.932209+00:00
-- url     : https://prove2.me/theorems/0a7278e3-81a8-4581-ad18-3443cb29b3e8
-- title:
--   contains rfl: contains rfl
-- statement:
--   The contains rfl construction uses the contains rfl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/Containment.lean#L25-L25
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/Containment.lean#L25-L25

module
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_ScoutForbiddenMatrixContainment
set_option autoImplicit true
@[expose] public section
public section
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]
  {P : α → β → Prop} {M : γ → δ → Prop}

theorem contains_rfl {M : γ → δ → Prop} : Contains M M := by sorry

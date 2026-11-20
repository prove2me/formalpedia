-- Prove2me | Theorems.Thm_contains_of_isEmpty
-- name    : contains_of_isEmpty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:13:16.667563+00:00
-- url     : https://prove2.me/theorems/52385d82-4ee8-4bd7-91c4-10a1488c2936
-- title:
--   contains of is Empty: contains of is Empty
-- statement:
--   The contains of is Empty construction uses the contains of is Empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/Containment.lean#L27-L28
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/Containment.lean#L27-L28

module
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_ScoutForbiddenMatrixContainment
set_option autoImplicit true
@[expose] public section
public section
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]
  {P : α → β → Prop} {M : γ → δ → Prop}

theorem contains_of_isEmpty [IsEmpty α] [IsEmpty β] : Contains P M := by sorry

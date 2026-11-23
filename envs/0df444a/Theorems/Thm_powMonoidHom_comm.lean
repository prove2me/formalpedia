-- Prove2me | Theorems.Thm_powMonoidHom_comm
-- name    : powMonoidHom_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:48.517061+00:00
-- url     : https://prove2.me/theorems/a554f906-59e0-4727-9c31-f3f2b41f6a43
-- title:
--   pow Monoid Hom comm: pow Monoid Hom comm
-- statement:
--   The pow Monoid Hom comm construction uses the pow Monoid Hom comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Algebra/Group/Hom/Basic.lean#L3-L5
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Algebra/Group/Hom/Basic.lean#L3-L5

import Mathlib.Algebra.Group.Hom.Basic
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Hom_Basic
set_option autoImplicit false

theorem powMonoidHom_comm {α : Type*} {β : Type*} {n : ℕ} [CommMonoid α] [CommMonoid β] {f : α →* β} :
    (powMonoidHom n).comp f = f.comp (powMonoidHom n) := by sorry

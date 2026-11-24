-- Prove2me | Theorems.Thm_imageFinite
-- name    : imageFinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:24.178536+00:00
-- url     : https://prove2.me/theorems/77d90513-6268-42fa-8393-5a6b3d095d6d
-- title:
--   image Finite: image Finite
-- statement:
--   The image Finite construction uses the image Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Antoine-dSG/frieze_patterns/blob/4e921473387f925942f0b95f3853c59b33670282/FriezePatterns/chapter1.lean#L174-L198
-- source:
--   https://github.com/Antoine-dSG/frieze_patterns/blob/4e921473387f925942f0b95f3853c59b33670282/FriezePatterns/chapter1.lean#L174-L198

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Definitions.Def_FriezePatterns_chapter1
set_option autoImplicit true

theorem imageFinite (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : Finite (Set.range f) := by sorry

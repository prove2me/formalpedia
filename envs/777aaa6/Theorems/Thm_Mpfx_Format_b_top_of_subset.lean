-- Prove2me | Theorems.Thm_Mpfx_Format_b_top_of_subset
-- name    : Mpfx.Format.b_top_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:03.819016+00:00
-- url     : https://prove2.me/theorems/083da2d5-8b64-4924-b029-ca1e75e9171b
-- title:
--   Format: b top of subset
-- statement:
--   An unbounded `F₁` has powers of two above any bound, so it fits only in an
--   unbounded `F₂`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L187-L196
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L187-L196

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.b_top_of_subset {F₁ F₂ : Format} (hp : F₁.p ≠ 0) (hb : F₁.b = ⊤) (h : F₁ ⊆ F₂) :
    F₂.b = ⊤ := by sorry

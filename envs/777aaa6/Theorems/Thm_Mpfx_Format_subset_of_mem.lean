-- Prove2me | Theorems.Thm_Mpfx_Format_subset_of_mem
-- name    : Mpfx.Format.subset_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:47:23.545791+00:00
-- url     : https://prove2.me/theorems/8f3f84da-1035-41e4-989c-59b50c295027
-- title:
--   Format: subset of mem
-- statement:
--   Build `F₁ ⊆ F₂` from the specials inclusion and numeric membership.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L38-L39
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L38-L39

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.subset_of_mem {F₁ F₂ : Format} (hs : F₁.specials ⊆ F₂.specials)
    (h : ∀ x : Dyadic, x ∈ F₁ → x ∈ F₂) : F₁ ⊆ F₂ := by sorry

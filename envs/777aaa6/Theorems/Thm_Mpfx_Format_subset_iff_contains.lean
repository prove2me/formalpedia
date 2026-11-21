-- Prove2me | Theorems.Thm_Mpfx_Format_subset_iff_contains
-- name    : Mpfx.Format.subset_iff_contains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:54:30.005569+00:00
-- url     : https://prove2.me/theorems/c2dd1b0c-49fd-4281-b79b-bc213580aa25
-- title:
--   Format: subset iff contains
-- statement:
--   **Completeness of the containment rules.** For `F₁` with a representable bound that
--   represents a nonzero value, `F₁ ⊆ F₂` holds exactly when one of the two rules
--   fires. No assumption on `F₂` is needed.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L389-L401
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L389-L401

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.subset_iff_contains {F₁ F₂ : Format} (hbr : BoundRep F₁) (hnt : F₁.Nontrivial) :
    F₁ ⊆ F₂ ↔ ContainsPrec F₁ F₂ ∨ ContainsSub F₁ F₂ := by sorry

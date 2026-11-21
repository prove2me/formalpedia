-- Prove2me | Theorems.Thm_Mpfx_Format_exp_le_of_subset
-- name    : Mpfx.Format.exp_le_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:00.717181+00:00
-- url     : https://prove2.me/theorems/150fb426-8f16-43bc-bb9c-4d270d7ea4c9
-- title:
--   Format: exp le of subset
-- statement:
--   **Necessity of `exp₂ ≤ exp₁`.** `F₁` is non-trivial, so `2^exp₁` is one of
--   its values (or, when `exp₁ = -∞`, so is `2^k` for arbitrarily small `k`), while
--   every value of `F₂` is a multiple of `2^exp₂`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L218-L256
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L218-L256

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.exp_le_of_subset {F₁ F₂ : Format} (hnt : F₁.Nontrivial) (h : F₁ ⊆ F₂) :
    F₂.exp ≤ F₁.exp := by sorry

-- Prove2me | Theorems.Thm_Mpfx_Format_containsPrec
-- name    : Mpfx.Format.containsPrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:39:07.878347+00:00
-- url     : https://prove2.me/theorems/cb109238-dd3b-4d68-95e2-6a04e96c2dea
-- title:
--   Format: contains Prec
-- statement:
--   **𝒜-Contains-Prec**. If `p₁ ≤ p₂`, `exp₂ ≤ exp₁`, `b₁ ≤ b₂` and `S₁ ⊆ S₂`,
--   then `𝒜(p₁, exp₁, b₁, S₁) ⊆ 𝒜(p₂, exp₂, b₂, S₂)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L64-L71
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L64-L71

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.containsPrec {F₁ F₂ : Format}
    (hp : F₁.p ≤ F₂.p) (he : F₂.exp ≤ F₁.exp) (hb : F₁.b ≤ F₂.b)
    (hs : F₁.specials ⊆ F₂.specials) : F₁ ⊆ F₂ := by sorry

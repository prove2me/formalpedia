-- Prove2me | Theorems.Thm_Mpfx_Format_containsSub
-- name    : Mpfx.Format.containsSub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:20.573199+00:00
-- url     : https://prove2.me/theorems/90775281-5297-4cdb-b88d-84b5f09708d7
-- title:
--   Format: contains Sub
-- statement:
--   **𝒜-Contains-Sub**. If `F₁`'s bound is at most `2^(exp₁ + p₂)`
--   (so every value of `F₁` fits in `F₂.p = p₂` bits at exponent `exp₁`), plus
--   the standard quantum, bound and specials orderings, then `F₁ ⊆ F₂` — even when
--   `F₁.p > F₂.p`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L111-L150
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L111-L150

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.containsSub {F₁ F₂ : Format}
    {exp₁ : ℤ} (he₁ : F₁.exp = (exp₁ : QExp))
    {p₂ : ℕ} (hp₂pos : 0 < p₂) (hp₂ : F₂.p = (p₂ : Prec))
    (hbprec : F₁.b ≤ ((nnPow (exp₁ + (p₂ : ℤ)) : NonNegDyadic) : Bound))
    (he : F₂.exp ≤ F₁.exp)
    (hb : F₁.b ≤ F₂.b) (hs : F₁.specials ⊆ F₂.specials) :
    F₁ ⊆ F₂ := by sorry

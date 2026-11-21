-- Prove2me | Theorems.Thm_Mpfx_boundOK_of_between
-- name    : Mpfx.boundOK_of_between
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:29:39.358835+00:00
-- url     : https://prove2.me/theorems/ee18a5bb-cb17-45f3-8aa9-20ee35f60ac3
-- title:
--   Mpfx: bound OK of between
-- statement:
--   A dyadic between two in-bound dyadics is in-bound.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L606-L618
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L606-L618

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.boundOK_of_between {b : Bound} {lo hi g : Dyadic}
    (hblo : Format.boundOK b lo) (hbhi : Format.boundOK b hi)
    (h1 : (lo : ℝ) ≤ (g : ℝ)) (h2 : (g : ℝ) ≤ (hi : ℝ)) :
    Format.boundOK b g := by sorry

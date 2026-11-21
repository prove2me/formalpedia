-- Prove2me | Theorems.Thm_Mpfx_mem_of_mem_unbounded_of_boundOK
-- name    : Mpfx.mem_of_mem_unbounded_of_boundOK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:31.3621+00:00
-- url     : https://prove2.me/theorems/b5b4556d-eb22-4652-a51f-503c8a95a1ca
-- title:
--   Mpfx: mem of mem unbounded of bound OK
-- statement:
--   Unbounded membership plus an explicit bound check gives bounded membership.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L626-L628
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L626-L628

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.mem_of_mem_unbounded_of_boundOK {F : FiniteFormat} {d : Dyadic}
    (h : d ∈ F.unbounded) (hb : Format.boundOK F.b d) : d ∈ F := by sorry

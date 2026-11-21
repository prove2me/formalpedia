-- Prove2me | Theorems.Thm_Mpfx_mem_unbounded_of_mem
-- name    : Mpfx.mem_unbounded_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:23:13.336686+00:00
-- url     : https://prove2.me/theorems/4dba3105-266d-4cf3-ad82-5c55da1e1c02
-- title:
--   Mpfx: mem unbounded of mem
-- statement:
--   Bounded membership weakens to unbounded membership (drop the bound check).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L621-L623
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L621-L623

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.mem_unbounded_of_mem {F : FiniteFormat} {d : Dyadic}
    (h : d ∈ F) : d ∈ F.unbounded := by sorry

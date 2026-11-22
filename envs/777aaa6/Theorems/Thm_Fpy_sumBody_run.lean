-- Prove2me | Theorems.Thm_Fpy_sumBody_run
-- name    : Fpy.sumBody_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:07:18.300693+00:00
-- url     : https://prove2.me/theorems/f6502ca9-343b-43bf-acd7-4a24e725cf9a
-- title:
--   Fpy: sum Body run
-- statement:
--   The Fpy construction uses the sum Body run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Sum.lean#L113-L139
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Sum.lean#L113-L139

import Definitions.Def_Fpy_Semantics
import Definitions.Def_Fpy_Ops
import Definitions.Def_Fpy_Sum
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
variable {C : Val} {r : Num → Num} (hr : C.rnd (fpy decode) = some r) (us : List Num)
include hr

theorem Fpy.sumBody_run :
    Exec Φ (Store.single "xs" (.list (us.map .num))) C sumBody (.ret (.num (sumVal r us))) := by sorry

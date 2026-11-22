-- Prove2me | Theorems.Thm_Fpy_fpyCtxFmt_sound
-- name    : Fpy.fpyCtxFmt_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:10:06.978193+00:00
-- url     : https://prove2.me/theorems/c944dca2-1244-4ef4-9691-f3f3196d4cb7
-- title:
--   Fpy: fpy Ctx Fmt sound
-- statement:
--   An Mpfx context rounds into its format and leaves the format's values
--   unchanged: the obligation `Analysis.Sound.ctxFmt`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Domain.lean#L138-L158
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Domain.lean#L138-L158

import Definitions.Def_Fpy_FormatInference_Defs
import Definitions.Def_Fpy_Ops
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Fpy_FormatInference_Domain
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.fpyCtxFmt_sound {decode : List (Label × Val) → Option RoundCtx} {C : Val} {FC : Fmt}
    {r : Num → Num} (hFC : fpyCtxFmt decode C = some FC) (hr : C.rnd (fpy decode) = some r) :
    (∀ n, r n ∈ FC.γ) ∧ ∀ n ∈ FC.γ, r n = n := by sorry

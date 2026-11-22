-- Prove2me | Theorems.Thm_Fpy_ArithOp_fmt_sound
-- name    : Fpy.ArithOp.fmt_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:37.671851+00:00
-- url     : https://prove2.me/theorems/b479a3fa-1091-42b3-ab69-62e14e17d049
-- title:
--   Arith Op: fmt sound
-- statement:
--   Each `op♯` bounds its operator's exact result.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L397-L430
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L397-L430

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.ArithOp.fmt_sound (c : Ceiling) {op : ArithOp} {ns : List Num} {Fs : List Fmt}
    {n : Num} (h : List.Forall₂ (fun n F => n ∈ F.γ) ns Fs) (hop : op.eval ns = some n) :
    n ∈ (op.fmt c Fs).γ := by sorry

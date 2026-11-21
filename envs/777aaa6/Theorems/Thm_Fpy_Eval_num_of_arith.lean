-- Prove2me | Theorems.Thm_Fpy_Eval_num_of_arith
-- name    : Fpy.Eval.num_of_arith
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:50:15.539105+00:00
-- url     : https://prove2.me/theorems/ed190ef9-f2cd-47ef-b990-da908b7b888a
-- title:
--   Eval: num of arith
-- statement:
--   An argument of a rounded operator evaluates to a number.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L222-L224
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L222-L224

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}

theorem Fpy.Eval.num_of_arith {op : L.ArithOp} {es : List (Expr L)} {v : Val} {e : Expr L}
    (h : Eval Φ σ C (.arith op es) v) (he : e ∈ es) : ∃ u, Eval Φ σ C e (.num u) := by sorry

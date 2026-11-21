-- Prove2me | Theorems.Thm_Fpy_eval_var_inv
-- name    : Fpy.eval_var_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:49:47.060864+00:00
-- url     : https://prove2.me/theorems/e512d7ee-b8bc-486f-8c04-42111027d6b8
-- title:
--   Fpy: eval var inv
-- statement:
--   The Fpy construction uses the eval var inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L203-L204
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L203-L204

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}

theorem Fpy.eval_var_inv {x : Var} {v : Val} (h : Eval Φ σ C (.var x) v) : σ x = some v := by sorry

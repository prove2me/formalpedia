-- Prove2me | Theorems.Thm_Fpy_Exec_withCtx_assign
-- name    : Fpy.Exec.withCtx_assign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:02.854652+00:00
-- url     : https://prove2.me/theorems/c4241644-1bcc-4dac-a0d5-fef4898dab50
-- title:
--   Exec: with Ctx assign
-- statement:
--   The Exec construction uses the with Ctx assign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L245-L247
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L245-L247

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}

theorem Fpy.Exec.withCtx_assign {e e' : Expr L} {y : Var} {o : Outcome}
    (h : Exec Φ σ C (.withCtx e (.assign y e')) o) : ∃ C' v, Eval Φ σ C' e' v := by sorry

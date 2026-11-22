-- Prove2me | Theorems.Thm_Fpy_eval_cmp
-- name    : Fpy.eval_cmp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:40.656234+00:00
-- url     : https://prove2.me/theorems/1aacf2fd-c15a-4073-8238-bef9e741ae07
-- title:
--   Fpy: eval cmp
-- statement:
--   The Fpy construction uses the eval cmp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L122-L136
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean#L122-L136

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}

theorem Fpy.eval_cmp {op : ExactOp} {k : Cmp} (hk : Cmp.ofOp op = some k) {σ : Store} {C : Val}
    {e₁ e₂ : Expr (fpy decode)} {b : Bool} (h : Eval Φ σ C (.exact op [e₁, e₂]) (.bool b)) :
    ∃ n₁ n₂, Eval Φ σ C e₁ (.num n₁) ∧ Eval Φ σ C e₂ (.num n₂) ∧ k.eval n₁ n₂ = b := by sorry

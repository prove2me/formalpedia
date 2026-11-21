-- Prove2me | Theorems.Thm_Fpy_EvalList_num_of_mem
-- name    : Fpy.EvalList.num_of_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:57:35.227578+00:00
-- url     : https://prove2.me/theorems/e9bbd398-eced-4cb0-8af7-c8f5ee279a06
-- title:
--   Eval List: num of mem
-- statement:
--   The Eval List construction uses the num of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L206-L219
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L206-L219

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}

theorem Fpy.EvalList.num_of_mem : ∀ {es : List (Expr L)} {ns : List Num},
    EvalList Φ σ C es (ns.map .num) → ∀ e ∈ es, ∃ u, Eval Φ σ C e (.num u) := by sorry

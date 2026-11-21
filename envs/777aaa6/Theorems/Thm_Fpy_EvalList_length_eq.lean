-- Prove2me | Theorems.Thm_Fpy_EvalList_length_eq
-- name    : Fpy.EvalList.length_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:54:17.150826+00:00
-- url     : https://prove2.me/theorems/5c0db188-d60b-4aad-b3e0-10b0dc93054e
-- title:
--   Eval List: length eq
-- statement:
--   The Eval List construction uses the length eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Semantics.lean#L159-L162
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Semantics.lean#L159-L162

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Fpy_Semantics
set_option autoImplicit true
open Fpy
variable {L : Signature}
variable (Φ : Program L)

theorem Fpy.EvalList.length_eq {σ : Store} {C : Val} :
    ∀ {es : List (Expr L)} {vs : List Val}, EvalList Φ σ C es vs → es.length = vs.length
  := by sorry

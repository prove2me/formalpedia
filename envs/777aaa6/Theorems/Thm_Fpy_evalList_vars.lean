-- Prove2me | Theorems.Thm_Fpy_evalList_vars
-- name    : Fpy.evalList_vars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:31:55.842924+00:00
-- url     : https://prove2.me/theorems/ea745b05-8a99-494a-b55a-226c3bdca0fe
-- title:
--   Fpy: eval List vars
-- statement:
--   The Fpy construction uses the eval List vars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L35-L45
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L35-L45

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}

theorem Fpy.evalList_vars {σ : Store} {C : Val} : ∀ {ys : List Var} {vs : List Val},
    EvalList Φ σ C (ys.map .var) vs ↔ List.Forall₂ (fun y v => σ y = some v) ys vs
  := by sorry

-- Prove2me | Theorems.Thm_P2M_Fpy_forall__updates_adf16c2a79da
-- name    : P2M_Fpy_forall__updates_adf16c2a79da
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:33:11.986869+00:00
-- url     : https://prove2.me/theorems/a1e07676-6a26-4704-bd70-3944e8c58b9c
-- title:
--   P2 M Fpy forall  updates adf16c2a79da: P2 M Fpy forall  updates adf16c2a79da
-- statement:
--   The P2 M Fpy forall  updates adf16c2a79da construction uses the P2 M Fpy forall  updates adf16c2a79da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L82-L89
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L82-L89

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}

theorem P2M_Fpy_forall__updates_adf16c2a79da {α : Type} :
    ∀ {f : Var → Option α} {ts : List Var} {xs : List α}, ts.Nodup → ts.length = xs.length →
      List.Forall₂ (fun t x => updates f ts xs t = some x) ts xs
  := by sorry

alias «Fpy».«forall₂_updates» := P2M_Fpy_forall__updates_adf16c2a79da

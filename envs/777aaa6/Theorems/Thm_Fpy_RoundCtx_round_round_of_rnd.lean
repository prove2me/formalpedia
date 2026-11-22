-- Prove2me | Theorems.Thm_Fpy_RoundCtx_round_round_of_rnd
-- name    : Fpy.RoundCtx.round_round_of_rnd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:31:54.255493+00:00
-- url     : https://prove2.me/theorems/2abaaf37-17df-4e69-a0b7-96d2a4ba0d28
-- title:
--   Round Ctx: round round of rnd
-- statement:
--   The Round Ctx construction uses the round round of rnd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L265-L273
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L265-L273

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}
variable {decode : List (Label × Val) → Option RoundCtx}

theorem Fpy.RoundCtx.round_round_of_rnd {c₁ c₂ : RoundCtx} {n : Num}
    (h : ∀ u, rnd c₂.F c₂.S c₂.O c₂.rm n = .value u →
      rnd c₁.F c₁.S c₁.O c₁.rm u.toReal = rnd c₁.F c₁.S c₁.O c₁.rm n) :
    c₁.round (c₂.round n) = c₁.round n := by sorry

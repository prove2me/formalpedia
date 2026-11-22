-- Prove2me | Theorems.Thm_Fpy_RoundCtx_round_round
-- name    : Fpy.RoundCtx.round_round
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:38:08.597436+00:00
-- url     : https://prove2.me/theorems/7734b519-4822-42f0-af2b-b6041cf68487
-- title:
--   Round Ctx: round round
-- statement:
--   A total double-rounding rule (`rndRTO_RN`, …) gives Split's condition.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L276-L280
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L276-L280

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

theorem Fpy.RoundCtx.round_round {c₁ c₂ : RoundCtx}
    (h : ∀ v u, rnd c₂.F c₂.S c₂.O c₂.rm v = .value u →
      rnd c₁.F c₁.S c₁.O c₁.rm u.toReal = rnd c₁.F c₁.S c₁.O c₁.rm v) (n : Num) :
    c₁.round (c₂.round n) = c₁.round n := by sorry

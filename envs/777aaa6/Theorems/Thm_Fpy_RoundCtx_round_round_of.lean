-- Prove2me | Theorems.Thm_Fpy_RoundCtx_round_round_of
-- name    : Fpy.RoundCtx.round_round_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:31:52.272958+00:00
-- url     : https://prove2.me/theorems/51ad5c4c-c6a9-40ab-aab6-aeb6f255d7a9
-- title:
--   Round Ctx: round round of
-- statement:
--   Double rounding at one input: a special through composing maps, and a
--   finite `x` that `F₂` keeps in bound and on which the finite rule holds.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L284-L303
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L284-L303

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

theorem Fpy.RoundCtx.round_round_of {c₁ c₂ : RoundCtx} (hS : c₂.S.Composes c₁.S c₁.O c₁.rm)
    {n : Num} (hn : ∀ x, n = .finite x → ∀ z, RoundsFinite c₂.F.unbounded c₂.rm x z →
      Format.boundOK c₂.F.b z ∧
        ∀ w, RoundsFinite c₁.F.unbounded c₁.rm z w → RoundsFinite c₁.F.unbounded c₁.rm x w) :
    c₁.round (c₂.round n) = c₁.round n := by sorry

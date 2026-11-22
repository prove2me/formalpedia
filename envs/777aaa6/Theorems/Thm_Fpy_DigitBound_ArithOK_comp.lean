-- Prove2me | Theorems.Thm_Fpy_DigitBound_ArithOK_comp
-- name    : Fpy.DigitBound.ArithOK.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:26:41.808676+00:00
-- url     : https://prove2.me/theorems/47694534-20f6-4615-bdbd-624282788fed
-- title:
--   Arith OK: comp
-- statement:
--   D-Arith's premise from Table 2's two columns.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L40-L50
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L40-L50

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}

theorem Fpy.DigitBound.ArithOK.comp {κ : Option SCtx} {op : ArithOp} {Is : List (Term × Term × Option Term)}
    {n₀ n₁ n₂ : ℕ} {Ψ₁ Ψ₂ : List Con} {l m l' m' : Term} (ho : OpOK op Is n₀ n₁ Ψ₁ l m)
    (hr : RndOK decode κ l m n₁ n₂ Ψ₂ l' m') (hF₁ : Fresh n₀ n₁ Ψ₁) (hF₂ : Fresh n₁ n₂ Ψ₂)
    (hκ : CtxBelow n₀ κ) : ArithOK decode κ op Is n₀ n₂ (Ψ₁ ++ Ψ₂) l' m' := by sorry

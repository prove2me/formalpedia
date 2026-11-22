-- Prove2me | solution 1 for Fpy.DigitBound.EInt.top_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:18:49.589896+00:00
-- url     : https://prove2.me/submissions/31f6e074-fe3e-476e-8dca-d99d058ff124

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
namespace EInt
theorem _root_.solution {a : EInt} (h : a ≠ ⊥) : ⊤ + a = ⊤ := by
  cases a using WithBotTop.rec with
  | bot => exact absurd rfl h
  | coe k => rfl
  | top => rfl
end EInt
end Fpy.DigitBound

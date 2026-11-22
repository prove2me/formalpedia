-- Prove2me | Definitions.Def_Fpy_DigitBound_Digits
-- name    : Fpy_DigitBound_Digits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:16:11.364625+00:00
-- url     : https://prove2.me/theorems/9a9c7a85-e5e1-4a0e-b221-401cdb761093
-- title:
--   Digits
-- statement:
--   Definitions and structural lemmas for Digits, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean

import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
namespace Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
end Fpy.DigitBound



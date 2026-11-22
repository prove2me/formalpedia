-- Prove2me | Definitions.Def_Fpy_DigitBound_Sum
-- name    : Fpy_DigitBound_Sum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:43:18.335499+00:00
-- url     : https://prove2.me/theorems/1340af08-f221-440e-a2bd-53a38b936673
-- title:
--   Sum
-- statement:
--   Definitions and structural lemmas for Sum, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
set_option autoImplicit true
namespace Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
variable {D : FormatDomain} {A : Analysis (fpy decode) D}
end Fpy.DigitBound



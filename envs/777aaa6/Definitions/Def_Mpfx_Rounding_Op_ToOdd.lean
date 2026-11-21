-- Prove2me | Definitions.Def_Mpfx_Rounding_Op_ToOdd
-- name    : Mpfx_Rounding_Op_ToOdd
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:43:25.733783+00:00
-- url     : https://prove2.me/theorems/876e2bd4-5a5e-4ba3-95e8-e3fa2260cb73
-- title:
--   To Odd
-- statement:
--   Definitions and structural lemmas for To Odd, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op/ToOdd.lean

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
namespace Mpfx
attribute [local instance] Classical.propDecidable
end Mpfx



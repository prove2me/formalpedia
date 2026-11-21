-- Prove2me | Definitions.Def_Mpfx_Rounding_Op_Nearest
-- name    : Mpfx_Rounding_Op_Nearest
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:43:18.585234+00:00
-- url     : https://prove2.me/theorems/a2b085fc-2d30-48cf-aec6-88bc733056ec
-- title:
--   Nearest
-- statement:
--   Definitions and structural lemmas for Nearest, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op/Nearest.lean

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
namespace Mpfx
attribute [local instance] Classical.propDecidable
end Mpfx



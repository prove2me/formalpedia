-- Prove2me | Definitions.Def_Mpfx_Rounding_Op
-- name    : Mpfx_Rounding_Op
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:44:06.671059+00:00
-- url     : https://prove2.me/theorems/62bf6a04-74d3-43aa-9e8b-2e1f2948c231
-- title:
--   Op
-- statement:
--   Definitions and structural lemmas for Op, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
set_option autoImplicit true
namespace Mpfx
attribute [local instance] Classical.propDecidable
end Mpfx



-- Prove2me | Definitions.Def_Mpfx_Rounding_Op_Directed
-- name    : Mpfx_Rounding_Op_Directed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:42:58.627983+00:00
-- url     : https://prove2.me/theorems/51d0953c-a0d2-487d-a3f4-0d6668860ebe
-- title:
--   Directed
-- statement:
--   Definitions and structural lemmas for Directed, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op/Directed.lean

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
namespace Mpfx
attribute [local instance] Classical.propDecidable
end Mpfx



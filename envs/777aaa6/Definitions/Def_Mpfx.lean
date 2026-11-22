-- Prove2me | Definitions.Def_Mpfx
-- name    : Mpfx
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:55:25.043182+00:00
-- url     : https://prove2.me/theorems/3ffe4627-02f4-41ff-95f0-7e3d1e7bde6f
-- title:
--   Mpfx
-- statement:
--   Definitions and structural lemmas for Mpfx, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx.lean

import Definitions.Def_Mpfx_DoubleRounding_Add
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_DoubleRounding_Div
import Definitions.Def_Mpfx_DoubleRounding_Mul
import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Sqrt
import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Dyadic
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_Utils
set_option autoImplicit true



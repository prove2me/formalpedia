-- Prove2me | solution 1 for Mpfx.FiniteFormat.unbounded_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:23:02.696941+00:00
-- url     : https://prove2.me/submissions/9a69ed86-75d7-4d6f-b23f-d13ed2f0f3f9

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) :
    F.unbounded.unbounded = F.unbounded := rfl
end Mpfx.FiniteFormat

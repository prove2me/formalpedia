-- Prove2me | solution 1 for Mpfx.FiniteFormat.unbounded_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:22:58.284408+00:00
-- url     : https://prove2.me/submissions/ba674a2c-70ce-4f47-bd9a-392a00235708

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) : F.unbounded.p = F.p := rfl
end Mpfx.FiniteFormat

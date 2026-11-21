-- Prove2me | solution 1 for Mpfx.FiniteFormat.unbounded_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:22:58.809181+00:00
-- url     : https://prove2.me/submissions/976750ef-02dc-44f8-8663-63ff85b62d59

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) : F.unbounded.exp = F.exp := rfl
end Mpfx.FiniteFormat

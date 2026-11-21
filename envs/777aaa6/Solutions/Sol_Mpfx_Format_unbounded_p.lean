-- Prove2me | solution 1 for Mpfx.Format.unbounded_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:22:04.580522+00:00
-- url     : https://prove2.me/submissions/956a9d9f-170f-49b2-b5a5-a043af0e36b1

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution (F : Format) : F.unbounded.p = F.p := rfl
end Mpfx.Format

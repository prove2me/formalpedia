-- Prove2me | solution 1 for Mpfx.FiniteFormat.unbounded_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:22:41.129162+00:00
-- url     : https://prove2.me/submissions/d1aa5837-f24b-4231-b3cd-a8b2ee02d89d

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) : F.unbounded.b = ⊤ := rfl
end Mpfx.FiniteFormat

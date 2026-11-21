-- Prove2me | solution 1 for Mpfx.Format.finite_mem_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:22:16.40255+00:00
-- url     : https://prove2.me/submissions/f3e85d69-a7f4-489d-8445-50ba9dfdbda3

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace Format
theorem _root_.solution {F : Format} {d : Dyadic} :
    WithSpecial.finite d ∈ F.values ↔ d ∈ F := Iff.rfl
end Format
end Mpfx

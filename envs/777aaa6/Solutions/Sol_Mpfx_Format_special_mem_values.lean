-- Prove2me | solution 1 for Mpfx.Format.special_mem_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:22:24.722786+00:00
-- url     : https://prove2.me/submissions/92d1d339-8603-4b0f-9f50-dfe904426ab7

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace Format
theorem _root_.solution {F : Format} {s : Special} :
    WithSpecial.special s ∈ F.values ↔ s ∈ F.specials := Iff.rfl
end Format
end Mpfx

-- Prove2me | solution 1 for Fpy.p_ne_one_of_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:33:05.314367+00:00
-- url     : https://prove2.me/submissions/f23a0383-d0f4-4ba1-99e4-fcc41b45be60

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower

set_option autoImplicit true
open Fpy
open Mpfx
namespace Fpy
theorem _root_.solution {F : FiniteFormat} (h : F.p = ⊤) : F.p ≠ ((1 : ℕ) : Prec) := by
  rw [h]; exact WithTop.top_ne_coe
end Fpy

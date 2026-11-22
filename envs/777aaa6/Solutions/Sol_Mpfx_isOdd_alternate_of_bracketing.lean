-- Prove2me | solution 1 for Mpfx.isOdd_alternate_of_bracketing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:26:50.985441+00:00
-- url     : https://prove2.me/submissions/30b9aeab-2055-4957-a17f-56439d988312

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_alternate_of_bracketing

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {x : ℝ}
    (h : ¬ F.IsUndefined .toOdd) {y y' : Dyadic}
    (hy : RoundsFinite F.unbounded .toNegative x y)
    (hy' : RoundsFinite F.unbounded .toPositive x y')
    (hne : x ≠ (y : ℝ)) :
    (F.IsOdd y' ↔ ¬ F.IsOdd y) :=
  (alternate_of_bracketing h hy hy' hne).1
end Mpfx

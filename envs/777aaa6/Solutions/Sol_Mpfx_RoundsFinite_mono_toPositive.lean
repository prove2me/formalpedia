-- Prove2me | solution 1 for Mpfx.RoundsFinite.mono_toPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:01:54.901909+00:00
-- url     : https://prove2.me/submissions/708963d0-b074-4215-a821-b3956f588515

import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Monotone

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {x x' : ℝ} {y y' : Dyadic}
    (hx : x ≤ x') (hy : RoundsFinite F .toPositive x y)
    (hy' : RoundsFinite F .toPositive x' y') : (y : ℝ) ≤ y' :=
  hy.2.2 y' hy'.1 (hx.trans hy'.2.1)
end RoundsFinite
end Mpfx

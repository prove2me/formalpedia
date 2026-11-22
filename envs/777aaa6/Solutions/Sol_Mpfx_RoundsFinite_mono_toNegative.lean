-- Prove2me | solution 1 for Mpfx.RoundsFinite.mono_toNegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:02:57.669187+00:00
-- url     : https://prove2.me/submissions/c9611046-56cf-4143-97a1-9d15316746d0

import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Monotone

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {x x' : ℝ} {y y' : Dyadic}
    (hx : x ≤ x') (hy : RoundsFinite F .toNegative x y)
    (hy' : RoundsFinite F .toNegative x' y') : (y : ℝ) ≤ y' :=
  hy'.2.2 y hy.1 (hy.2.1.trans hx)
end RoundsFinite
end Mpfx

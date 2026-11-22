-- Prove2me | solution 1 for Mpfx.rndUnbounded_satisfies_toNegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:03:18.551858+00:00
-- url     : https://prove2.me/submissions/2428ebfa-4913-4a16-9411-2bbbf6be45c4

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_floor


set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toNegative) :
    RoundsFinite F.unbounded .toNegative x (rndUnbounded F .toNegative x h) :=
  RoundsFinite.toNegative_floor F x
end Mpfx

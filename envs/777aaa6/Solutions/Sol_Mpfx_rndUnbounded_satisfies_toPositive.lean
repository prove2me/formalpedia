-- Prove2me | solution 1 for Mpfx.rndUnbounded_satisfies_toPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:13:52.442172+00:00
-- url     : https://prove2.me/submissions/e3832d20-50b1-4ff7-968b-ee182be6a295

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_ceil


set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toPositive) :
    RoundsFinite F.unbounded .toPositive x (rndUnbounded F .toPositive x h) :=
  RoundsFinite.toPositive_ceil F x
end Mpfx

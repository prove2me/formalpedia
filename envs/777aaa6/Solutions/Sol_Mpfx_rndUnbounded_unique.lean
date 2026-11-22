-- Prove2me | solution 1 for Mpfx.rndUnbounded_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:31:21.188473+00:00
-- url     : https://prove2.me/submissions/983c49b6-a861-42da-8e93-26199a416e77

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op
import Theorems.Thm_Mpfx_rndUnbounded_satisfies
import Theorems.Thm_Mpfx_RoundsFinite_unique


set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (rm : RoundingMode) (x : ℝ)
    (h : ¬ F.IsUndefined rm) {y : Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) :
    y = rndUnbounded F rm x h :=
  RoundsFinite.unique h hy (rndUnbounded_satisfies F rm x h)
end Mpfx

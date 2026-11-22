-- Prove2me | solution 1 for Mpfx.rndUnbounded_satisfies
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:26:59.132197+00:00
-- url     : https://prove2.me/submissions/95b8cdd7-dc3b-42da-9673-b42b846c0141

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op
import Theorems.Thm_Mpfx_rndUnbounded_satisfies_awayZero
import Theorems.Thm_Mpfx_rndUnbounded_satisfies_nearest
import Theorems.Thm_Mpfx_rndUnbounded_satisfies_toNegative
import Theorems.Thm_Mpfx_rndUnbounded_satisfies_toOdd
import Theorems.Thm_Mpfx_rndUnbounded_satisfies_toPositive
import Theorems.Thm_Mpfx_rndUnbounded_satisfies_toZero


set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (rm : RoundingMode) (x : ℝ)
    (h : ¬ F.IsUndefined rm) :
    RoundsFinite F.unbounded rm x (rndUnbounded F rm x h) := by
  cases rm with
  | toNegative => exact rndUnbounded_satisfies_toNegative F x h
  | toPositive => exact rndUnbounded_satisfies_toPositive F x h
  | toZero => exact rndUnbounded_satisfies_toZero F x h
  | awayZero => exact rndUnbounded_satisfies_awayZero F x h
  | toOdd => exact rndUnbounded_satisfies_toOdd F x h
  | nearest tb => exact rndUnbounded_satisfies_nearest F tb x h
end Mpfx

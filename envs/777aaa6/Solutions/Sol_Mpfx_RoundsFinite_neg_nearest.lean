-- Prove2me | solution 1 for Mpfx.RoundsFinite.neg_nearest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:15:18.882297+00:00
-- url     : https://prove2.me/submissions/188da232-a9b6-4cda-8c9c-f28cc9d1e5b5

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_RoundsFinite_neg_nearest_awayZero
import Theorems.Thm_Mpfx_RoundsFinite_neg_nearest_toEven

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution (F : FiniteFormat) (tb : TieBreak) (a : ℝ) (v : Dyadic) :
    RoundsFinite F (.nearest tb) a v ↔ RoundsFinite F (.nearest tb) (-a) (-v) := by
  cases tb with
  | toEven => exact RoundsFinite.neg_nearest_toEven F a v
  | awayZero => exact RoundsFinite.neg_nearest_awayZero F a v
end RoundsFinite
end Mpfx

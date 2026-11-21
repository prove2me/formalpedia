-- Prove2me | solution 1 for Mpfx.RoundsFinite.nearest_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:46:09.34518+00:00
-- url     : https://prove2.me/submissions/baff90f9-0f70-475e-892e-2c0d98f773a5

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F (.nearest tb) x y) {z : Dyadic}
    (hz : z ∈ F) (hzf : IsFaithfulRound F x z) :
    |x - (y : ℝ)| ≤ |x - (z : ℝ)| := by
  cases tb with
  | toEven => exact h.2.2.1 z hz hzf
  | awayZero => exact h.2.2.1 z hz hzf
end RoundsFinite
end Mpfx

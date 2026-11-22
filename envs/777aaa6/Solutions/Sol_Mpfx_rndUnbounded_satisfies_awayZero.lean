-- Prove2me | solution 1 for Mpfx.rndUnbounded_satisfies_awayZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:13:54.655988+00:00
-- url     : https://prove2.me/submissions/af9993d4-1e37-4fd6-9ce0-903ae8879ed9

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_floor
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_iff_awayZero_of_nonpos
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_ceil
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_iff_awayZero_of_nonneg


set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .awayZero) :
    RoundsFinite F.unbounded .awayZero x (rndUnbounded F .awayZero x h) := by
  unfold rndUnbounded
  by_cases hx : 0 ≤ x
  · rw [show rndInt F .awayZero x _ = _ from if_pos hx]
    exact (RoundsFinite.toPositive_iff_awayZero_of_nonneg F.unbounded hx _).mp
      (RoundsFinite.toPositive_ceil F x)
  · rw [show rndInt F .awayZero x _ = _ from if_neg hx]
    exact (RoundsFinite.toNegative_iff_awayZero_of_nonpos F.unbounded (not_le.mp hx).le _).mp
      (RoundsFinite.toNegative_floor F x)
end Mpfx

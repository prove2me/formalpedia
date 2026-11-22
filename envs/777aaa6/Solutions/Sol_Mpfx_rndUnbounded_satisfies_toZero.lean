-- Prove2me | solution 1 for Mpfx.rndUnbounded_satisfies_toZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:13:54.187294+00:00
-- url     : https://prove2.me/submissions/a57aa069-4e18-4f09-b510-4bb852c2e954

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_floor
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_iff_toZero_of_nonneg
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_ceil
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_iff_toZero_of_nonpos


set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toZero) :
    RoundsFinite F.unbounded .toZero x (rndUnbounded F .toZero x h) := by
  unfold rndUnbounded
  by_cases hx : 0 ≤ x
  · rw [show rndInt F .toZero x _ = _ from if_pos hx]
    exact (RoundsFinite.toNegative_iff_toZero_of_nonneg F.unbounded hx _).mp
      (RoundsFinite.toNegative_floor F x)
  · rw [show rndInt F .toZero x _ = _ from if_neg hx]
    exact (RoundsFinite.toPositive_iff_toZero_of_nonpos F.unbounded (not_le.mp hx).le _).mp
      (RoundsFinite.toPositive_ceil F x)
end Mpfx

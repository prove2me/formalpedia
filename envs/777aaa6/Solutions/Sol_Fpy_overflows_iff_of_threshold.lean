-- Prove2me | solution 1 for Fpy.overflows_iff_of_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:52:52.330551+00:00
-- url     : https://prove2.me/submissions/c2ba5f02-a092-4a3b-b696-0733824521f5

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
import Theorems.Thm_Fpy_Equiv_mono
import Theorems.Thm_Fpy_Outcome_Agree_mono
import Theorems.Thm_Fpy_Store_Agree_mono
import Theorems.Thm_Mpfx_RoundsFinite_mono
import Theorems.Thm_Mpfx_RoundsFinite_unique
import Theorems.Thm_Mpfx_boundOK_of_between
import Theorems.Thm_Mpfx_rndUnbounded_satisfies


set_option autoImplicit true
open Fpy
open Mpfx
namespace Fpy
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode}
    (h : ¬ F.IsUndefined rm) {θ : ℝ} (hlo : Format.boundOK F.b (rndUnbounded F rm (-θ) h))
    (hhi : Format.boundOK F.b (rndUnbounded F rm θ h))
    (hout : ∀ y, y < -θ ∨ θ < y → ¬ Format.boundOK F.b (rndUnbounded F rm y h)) (y : ℝ) :
    Overflows F rm y ↔ y < -θ ∨ θ < y := by
  refine ⟨fun ⟨z, hz, hnb⟩ => ?_, fun hy => ⟨_, rndUnbounded_satisfies F rm y h, hout y hy⟩⟩
  rw [RoundsFinite.unique h hz (rndUnbounded_satisfies F rm y h)] at hnb
  by_contra hy
  push Not at hy
  exact hnb (boundOK_of_between hlo hhi
    (RoundsFinite.mono h hy.1 (rndUnbounded_satisfies _ _ _ _) (rndUnbounded_satisfies _ _ _ _))
    (RoundsFinite.mono h hy.2 (rndUnbounded_satisfies _ _ _ _) (rndUnbounded_satisfies _ _ _ _)))
end Fpy

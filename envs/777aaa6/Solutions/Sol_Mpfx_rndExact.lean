-- Prove2me | solution 1 for Mpfx.rndExact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:17:10.926104+00:00
-- url     : https://prove2.me/submissions/5dedf886-231f-4d82-9795-ed50bb8fe971

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Theorems.Thm_Mpfx_IsFaithfulRound_eq_of_mem
import Theorems.Thm_Mpfx_RoundsFinite_eq_of_mem


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    {v : Dyadic} (hv : v ∈ F₂) {z w : Dyadic}
    (hz : RoundsFinite F₂ rm₂ (v : ℝ) z) (hw : RoundsFinite F₁ rm₁ (z : ℝ) w) :
    RoundsFinite F₁ rm₁ (v : ℝ) w := by
  rw [RoundsFinite.eq_of_mem hv hz] at hw
  exact hw
end Mpfx

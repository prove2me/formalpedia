-- Prove2me | solution 1 for Mpfx.roundsRTN_RTN_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:57:11.486971+00:00
-- url     : https://prove2.me/submissions/9f93b347-b5b1-485a-b964-2211eec22f94

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toNegative x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w :=
  ⟨hw.1, hw.2.1.trans hz.2.1, fun v hv hvx => hw.2.2 v hv (hz.2.2 v (hsub v hv) hvx)⟩
end Mpfx

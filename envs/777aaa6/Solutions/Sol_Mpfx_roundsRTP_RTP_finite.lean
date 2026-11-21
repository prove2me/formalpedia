-- Prove2me | solution 1 for Mpfx.roundsRTP_RTP_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:57:11.918174+00:00
-- url     : https://prove2.me/submissions/b47e9e3d-55ae-4eb5-a863-a80c2c449006

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
    (hz : RoundsFinite F₂ .toPositive x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w :=
  ⟨hw.1, hz.2.1.trans hw.2.1, fun v hv hxv => hw.2.2 v hv (hz.2.2 v (hsub v hv) hxv)⟩
end Mpfx

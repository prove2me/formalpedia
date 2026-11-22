-- Prove2me | solution 1 for Mpfx.roundsRTO_RAZ_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:49:59.913436+00:00
-- url     : https://prove2.me/submissions/86d57671-7ac1-4064-9b29-718d2870fede

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Theorems.Thm_Mpfx_roundsRTO_RTN_finite
import Theorems.Thm_Mpfx_roundsRTO_RTP_finite
import Theorems.Thm_Mpfx_IsFaithfulRound_nonneg
import Theorems.Thm_Mpfx_IsFaithfulRound_nonpos
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_iff_awayZero_of_nonpos
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_iff_awayZero_of_nonneg

section
namespace Mpfx
private theorem awayZero_of_directed {F₁ F₂ : FiniteFormat} {x : ℝ} {z w : Dyadic}
    (hzx : IsFaithfulRound F₂ x z)
    (hdn : x ≤ 0 → RoundsFinite F₁ .toNegative (z : ℝ) w → RoundsFinite F₁ .toNegative x w)
    (hup : 0 ≤ x → RoundsFinite F₁ .toPositive (z : ℝ) w → RoundsFinite F₁ .toPositive x w)
    (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) : RoundsFinite F₁ .awayZero x w := by
  rcases le_total 0 x with hx | hx
  · exact (RoundsFinite.toPositive_iff_awayZero_of_nonneg F₁ hx w).mp
      (hup hx ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F₁ (hzx.nonneg hx) w).mpr hw))
  · exact (RoundsFinite.toNegative_iff_awayZero_of_nonpos F₁ hx w).mp
      (hdn hx ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F₁ (hzx.nonpos hx) w).mpr hw))
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) :
    RoundsFinite F₁ .awayZero x w :=
  awayZero_of_directed hz.isFaithfulRound
    (fun _ => roundsRTO_RTN_finite hsub hz) (fun _ => roundsRTO_RTP_finite hsub hz) hw
end Mpfx

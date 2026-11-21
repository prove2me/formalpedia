-- Prove2me | solution 1 for Mpfx.LocalDoubleRounding.not_overflows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:47:43.792874+00:00
-- url     : https://prove2.me/submissions/50009575-3c7b-4237-ab05-76d095d983ed

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace LocalDoubleRounding
theorem _root_.solution {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    {L : ℝ → Prop} (h : LocalDoubleRounding F₁ F₂ rm₁ rm₂ L) {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ rm₂ x z) (hw : RoundsInBound F₁ rm₁ (z : ℝ) w) :
    ¬ Overflows F₁ rm₁ x := by
  rintro ⟨y, hy, hby⟩
  exact hby (h.agree (h.pin_double hz hw) hz.1 hw.1 hy ▸ hw.2)
end LocalDoubleRounding
end Mpfx

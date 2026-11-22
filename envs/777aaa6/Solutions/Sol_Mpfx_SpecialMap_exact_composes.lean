-- Prove2me | solution 1 for Mpfx.SpecialMap.exact_composes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:50:02.912339+00:00
-- url     : https://prove2.me/submissions/5a2d24ed-2591-402b-9dbc-de148bd3812f

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_rnd_special
attribute [local simp] Mpfx.rnd_special



set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace SpecialMap
theorem _root_.solution {F₂ : FiniteFormat} (h₂ : ∀ s, s ∈ F₂.specials)
    {F₁ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat} {O₁ : OverflowMap F₁.toFormat}
    {rm₁ : RoundingMode} : (SpecialMap.exact F₂.toFormat h₂).Composes S₁ O₁ rm₁ :=
  fun _ => rnd_special _ _ _ _ _
end SpecialMap
end Mpfx

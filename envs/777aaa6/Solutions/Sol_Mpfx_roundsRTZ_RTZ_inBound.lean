-- Prove2me | solution 1 for Mpfx.roundsRTZ_RTZ_inBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:42:28.656553+00:00
-- url     : https://prove2.me/submissions/76b820c8-38ca-4e99-bd9b-1b7ac9c98f71

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_LocalDoubleRounding_inBound
import Theorems.Thm_Mpfx_withBound_subset_of_boundOK
import Theorems.Thm_Mpfx_localDoubleRounding_of_above
import Theorems.Thm_Mpfx_FiniteFormat_subset_unbounded
import Theorems.Thm_Mpfx_not_isUndefined_toZero
import Theorems.Thm_Mpfx_roundsRTZ_RTZ_finite

section
namespace Mpfx
private theorem withBoundFF_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {T : NonNegDyadic} (hT : Format.boundOK F₁.toFormat.boundAfterNext T.val) :
    (F₁.withBoundFF T).toFormat ⊆ F₂.unbounded.toFormat :=
  ((withBound_subset_of_boundOK _ hT).trans hsub).trans F₂.subset_unbounded
private theorem localDoubleRounding_RTZ_RTZ {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat) :
    LocalDoubleRounding F₁ F₂ .toZero .toZero (BelowValue F₁ F₁.toFormat.boundAfterNext) :=
  localDoubleRounding_of_above (not_isUndefined_toZero F₁)
    (fun hT hTB => hsub _ ⟨hT.1, hT.2.1, hTB⟩)
    (fun _ hTB => roundsRTZ_RTZ_finite (withBoundFF_subset hsub hTB))
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (x : ℝ) :
    Overflows F₁ .toZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toZero x z ∧
      RoundsInBound F₁ .toZero (z : ℝ) w ∧
      RoundsInBound F₁ .toZero x w) :=
  (localDoubleRounding_RTZ_RTZ hsub).inBound (not_isUndefined_toZero F₁)
    (not_isUndefined_toZero F₂) x
end Mpfx

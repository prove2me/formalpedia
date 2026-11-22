-- Prove2me | solution 1 for Mpfx.roundsRTO_RTO_inBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:42:46.376028+00:00
-- url     : https://prove2.me/submissions/f613e8c2-0db7-4f63-a9b8-d71b1fd29c27

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_LocalDoubleRounding_inBound
import Theorems.Thm_Mpfx_withBound_subset_of_boundOK
import Theorems.Thm_Mpfx_localDoubleRounding_of_above
import Theorems.Thm_Mpfx_FiniteFormat_subset_unbounded
import Theorems.Thm_Mpfx_not_isUndefined_of_two_le_p
import Theorems.Thm_Mpfx_roundsRTO_RTO_finite

section
namespace Mpfx
private theorem withBoundFF_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {T : NonNegDyadic} (hT : Format.boundOK F₁.toFormat.boundAfterNext T.val) :
    (F₁.withBoundFF T).toFormat ⊆ F₂.unbounded.toFormat :=
  ((withBound_subset_of_boundOK _ hT).trans hsub).trans F₂.subset_unbounded
private theorem localDoubleRounding_RTO_RTO {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd) :
    LocalDoubleRounding F₁ F₂ .toOdd .toOdd (BelowValue F₁ F₁.toFormat.boundAfterNext) :=
  localDoubleRounding_of_above h₁u (fun hT hTB => hsub _ ⟨hT.1, hT.2.1, hTB⟩)
    (fun _ hTB => roundsRTO_RTO_finite (withBoundFF_subset hsub hTB) hp_F₂)
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined .toOdd) (x : ℝ) :
    Overflows F₁ .toOdd x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ .toOdd (z : ℝ) w ∧
      RoundsInBound F₁ .toOdd x w) :=
  (localDoubleRounding_RTO_RTO hsub hp_F₂ h₁u).inBound h₁u
    (not_isUndefined_of_two_le_p hp_F₂) x
end Mpfx

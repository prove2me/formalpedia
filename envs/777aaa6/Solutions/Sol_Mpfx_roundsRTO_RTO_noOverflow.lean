-- Prove2me | solution 1 for Mpfx.roundsRTO_RTO_noOverflow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:42:56.671731+00:00
-- url     : https://prove2.me/submissions/727d15a4-e640-46df-9d1a-a635bc7d1763

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_LocalDoubleRounding_not_overflows
import Theorems.Thm_Mpfx_withBound_subset_of_boundOK
import Theorems.Thm_Mpfx_localDoubleRounding_of_above
import Theorems.Thm_Mpfx_FiniteFormat_subset_unbounded
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
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ .toOdd (z : ℝ) w) :
    ¬ Overflows F₁ .toOdd x :=
  (localDoubleRounding_RTO_RTO hsub hp_F₂ h₁u).not_overflows hz hw
end Mpfx

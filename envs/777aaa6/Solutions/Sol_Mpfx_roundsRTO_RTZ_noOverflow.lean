-- Prove2me | solution 1 for Mpfx.roundsRTO_RTZ_noOverflow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:43:10.225309+00:00
-- url     : https://prove2.me/submissions/fefe9222-1923-43f5-a300-2f236534adf2

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_LocalDoubleRounding_not_overflows
import Theorems.Thm_Mpfx_withBound_subset_of_boundOK
import Theorems.Thm_Mpfx_localDoubleRounding_of_above
import Theorems.Thm_Mpfx_FiniteFormat_subset_unbounded
import Theorems.Thm_Mpfx_mem_extend_one_withBound_of_mem_unbounded
import Theorems.Thm_Mpfx_not_isUndefined_toZero
import Theorems.Thm_Mpfx_roundsRTO_RTZ_finite_of_extend
import Theorems.Thm_Mpfx_two_le_p_of_nontrivial

section
namespace Mpfx
private theorem withBoundFF_extend_one_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {T : NonNegDyadic} (hT : Format.boundOK F₁.toFormat.boundAfterNext T.val) :
    ((F₁.withBoundFF T).extend 1).toFormat ⊆ F₂.unbounded.toFormat :=
  ((withBound_subset_of_boundOK (F₁.extend 1).toFormat hT).trans hsub).trans
    F₂.subset_unbounded
private theorem localDoubleRounding_RTO_RTZ {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) :
    LocalDoubleRounding F₁ F₂ .toZero .toOdd (BelowValue F₁ F₁.toFormat.boundAfterNext) :=
  localDoubleRounding_of_above (not_isUndefined_toZero F₁)
    (fun hT hTB => hsub _ (mem_extend_one_withBound_of_mem_unbounded hT hTB))
    (fun _ hTB => roundsRTO_RTZ_finite_of_extend (withBoundFF_extend_one_subset hsub hTB) hp_F₂)
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ .toZero (z : ℝ) w) :
    ¬ Overflows F₁ .toZero x :=
  (localDoubleRounding_RTO_RTZ hsub (two_le_p_of_nontrivial hsub hnt)).not_overflows hz hw
end Mpfx

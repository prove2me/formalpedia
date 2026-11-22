-- Prove2me | solution 1 for Mpfx.roundsRAZ_RAZ_inBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:40:53.74524+00:00
-- url     : https://prove2.me/submissions/6d5d5803-814f-402e-8d13-9ba761bef488

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_LocalDoubleRounding_inBound
import Theorems.Thm_Mpfx_localDoubleRounding_of_below
import Theorems.Thm_Mpfx_withBound_subset_of_boundOK
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_FiniteFormat_subset_unbounded
import Theorems.Thm_Mpfx_Format_abs_mem
import Theorems.Thm_Mpfx_boundOK_of_abs_le
import Theorems.Thm_Mpfx_not_isUndefined_awayZero
import Theorems.Thm_Mpfx_roundsRAZ_RAZ_finite
attribute [local simp] Mpfx.Dyadic.coe_abs


section
namespace Mpfx
private theorem localDoubleRounding_RAZ_RAZ {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    LocalDoubleRounding F₁ F₂ .awayZero .awayZero (BelowValue F₁ F₁.b) := by
  have habs : ∀ {v : Dyadic}, v ∈ F₁.unbounded → Format.boundOK F₁.b v →
      Dyadic.abs v ∈ F₁.unbounded ∧ Format.boundOK F₁.b (Dyadic.abs v) := fun hv hb =>
    ⟨Format.abs_mem hv, boundOK_of_abs_le (by rw [Dyadic.coe_abs, abs_abs]) hb⟩
  refine localDoubleRounding_of_below (not_isUndefined_awayZero F₁)
    (fun hT hTB => hsub _ ⟨hT.1, hT.2.1, hTB⟩)
    (fun _ hTB => roundsRAZ_RAZ_finite
      (((withBound_subset_of_boundOK F₁.toFormat hTB).trans hsub).trans F₂.subset_unbounded))
    (fun ⟨hy, hby⟩ => ?_) (fun ⟨hz, _⟩ ⟨hw, hbw⟩ => ?_)
  · obtain ⟨h1, h2⟩ := habs hy.1 hby
    exact ⟨_, h1, h2, by rw [Dyadic.coe_abs]; exact hy.2.1⟩
  · obtain ⟨h1, h2⟩ := habs hw.1 hbw
    exact ⟨_, h1, h2, by rw [Dyadic.coe_abs]; exact hz.2.1.trans hw.2.1⟩
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (x : ℝ) :
    Overflows F₁ .awayZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .awayZero x z ∧
      RoundsInBound F₁ .awayZero (z : ℝ) w ∧
      RoundsInBound F₁ .awayZero x w) :=
  (localDoubleRounding_RAZ_RAZ hsub).inBound (not_isUndefined_awayZero F₁)
    (not_isUndefined_awayZero F₂) x
end Mpfx

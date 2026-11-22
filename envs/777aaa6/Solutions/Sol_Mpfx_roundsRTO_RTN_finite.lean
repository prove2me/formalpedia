-- Prove2me | solution 1 for Mpfx.roundsRTO_RTN_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:31:27.897328+00:00
-- url     : https://prove2.me/submissions/8781c3f0-3d07-4959-960c-5695856c53b7

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Theorems.Thm_Mpfx_toOdd_notMem_of_extend_subset
import Theorems.Thm_Mpfx_Dyadic_IsRepresentableAtP_ne_zero
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_ne_zero
import Theorems.Thm_Mpfx_FiniteFormat_zero_mem
import Theorems.Thm_Mpfx_Format_self_subset_extend
import Theorems.Thm_Mpfx_Format_zero_mem
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero
import Theorems.Thm_Mpfx_extend_one_subset_of_withBound_subset
import Theorems.Thm_Mpfx_isFaithfulRound_iff_directed
import Theorems.Thm_Mpfx_two_le_p_or_trivial_of_extend_one_withBound_subset
attribute [local simp] Mpfx.Dyadic.coe_real_zero


section
namespace Mpfx
private theorem toOdd_eq_zero_of_eq_zero {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hz : RoundsFinite F .toOdd x z) (hz0 : (z : ℝ) = 0) : x = 0 := by
  by_contra hx
  exact (hz.2.2 (by rw [hz0]; exact hx)).ne_zero (eq_zero_of_coe_real_zero hz0)
private theorem toOdd_toNegative {F₁ F₂ : FiniteFormat}
    (hmem : ∀ v : Dyadic, v ∈ F₁ → v ∈ F₂) {x : ℝ} {z w : Dyadic}
    (hnot : x ≠ (z : ℝ) → z ∉ F₁)
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w := by
  obtain ⟨hwF₁, hwz, hw_max⟩ := hw
  rcases isFaithfulRound_iff_directed.mp hz.isFaithfulRound with
    ⟨-, hzx, hz_max⟩ | ⟨-, hxz, hz_min⟩
  · exact ⟨hwF₁, hwz.trans hzx, fun v hv hvx => hw_max v hv (hz_max v (hmem v hv) hvx)⟩
  · refine ⟨hwF₁, ?_, fun v hv hvx => hw_max v hv (hvx.trans hxz)⟩
    by_contra hxw
    push Not at hxw
    have hwz' : (w : ℝ) = z := le_antisymm hwz (hz_min w (hmem w hwF₁) hxw.le)
    exact hnot (hxw.trans_eq hwz').ne (Dyadic.ext_real hwz' ▸ hwF₁)
private theorem toOdd_directed_facts {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z : Dyadic} (hz : RoundsFinite F₂ .toOdd x z) :
    (∀ v : Dyadic, v ∈ F₁ → v ∈ F₂) ∧ (x ≠ (z : ℝ) → z ∉ F₁) := by
  rcases two_le_p_or_trivial_of_extend_one_withBound_subset hsub with hp | htriv
  · have h := extend_one_subset_of_withBound_subset hsub
    exact ⟨fun v hv => h v (Format.self_subset_extend _ 1 v hv),
      toOdd_notMem_of_extend_subset h hp hz⟩
  · refine ⟨fun v hv => ?_, fun hxz hzF =>
      hxz ((toOdd_eq_zero_of_eq_zero hz (htriv z hzF)).trans (htriv z hzF).symm)⟩
    rw [Dyadic.ext_real (by rw [htriv v hv, Dyadic.coe_real_zero] : (v : ℝ) = (0 : Dyadic))]
    exact F₂.zero_mem
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w :=
  toOdd_toNegative (toOdd_directed_facts hsub hz).1 (toOdd_directed_facts hsub hz).2 hz hw
end Mpfx

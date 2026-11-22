-- Prove2me | solution 1 for Mpfx.roundsRTO_RTP_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:31:41.083437+00:00
-- url     : https://prove2.me/submissions/c4da0bf0-3b8a-4eb7-8819-122baf91243d

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
private theorem toOdd_toPositive {F₁ F₂ : FiniteFormat}
    (hmem : ∀ v : Dyadic, v ∈ F₁ → v ∈ F₂) {x : ℝ} {z w : Dyadic}
    (hnot : x ≠ (z : ℝ) → z ∉ F₁)
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w := by
  obtain ⟨hwF₁, hzw, hw_min⟩ := hw
  rcases isFaithfulRound_iff_directed.mp hz.isFaithfulRound with
    ⟨-, hzx, hz_max⟩ | ⟨-, hxz, hz_min⟩
  · refine ⟨hwF₁, ?_, fun v hv hxv => hw_min v hv (hzx.trans hxv)⟩
    by_contra hwx
    push Not at hwx
    have hwz' : (w : ℝ) = z := le_antisymm (hz_max w (hmem w hwF₁) hwx.le) hzw
    exact hnot (hwz'.symm.trans_lt hwx).ne' (Dyadic.ext_real hwz' ▸ hwF₁)
  · exact ⟨hwF₁, hxz.trans hzw, fun v hv hxv => hw_min v hv (hz_min v (hmem v hv) hxv)⟩
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
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w :=
  toOdd_toPositive (toOdd_directed_facts hsub hz).1 (toOdd_directed_facts hsub hz).2 hz hw
end Mpfx

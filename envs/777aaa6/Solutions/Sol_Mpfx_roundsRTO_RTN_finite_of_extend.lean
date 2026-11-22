-- Prove2me | solution 1 for Mpfx.roundsRTO_RTN_finite_of_extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:22:57.017594+00:00
-- url     : https://prove2.me/submissions/7e57c66c-d4a1-4f5b-9edf-ed6c87219587

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
import Theorems.Thm_Mpfx_toOdd_notMem_of_extend_subset
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_Format_self_subset_extend
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_isFaithfulRound_iff_directed

section
namespace Mpfx
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
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w :=
  toOdd_toNegative (fun v hv => hsub v (Format.self_subset_extend _ 1 v hv))
    (toOdd_notMem_of_extend_subset hsub hp_F₂ hz) hz hw
end Mpfx

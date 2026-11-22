-- Prove2me | solution 1 for Mpfx.roundsRTO_RTP_finite_of_extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:22:57.71682+00:00
-- url     : https://prove2.me/submissions/941a92d4-e47b-40aa-bf8f-c013d73fbe60

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
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w :=
  toOdd_toPositive (fun v hv => hsub v (Format.self_subset_extend _ 1 v hv))
    (toOdd_notMem_of_extend_subset hsub hp_F₂ hz) hz hw
end Mpfx

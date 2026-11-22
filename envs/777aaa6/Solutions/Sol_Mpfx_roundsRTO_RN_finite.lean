-- Prove2me | solution 1 for Mpfx.roundsRTO_RN_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:32:29.426872+00:00
-- url     : https://prove2.me/submissions/e1981ee0-8bc8-4e25-841d-666245ca1477

import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Theorems.Thm_Mpfx_roundsRTO_RN_finite_of_extend
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_extend_two_subset_of_withBound_subset
import Theorems.Thm_Mpfx_two_le_p_or_trivial_of_extend_two_withBound_subset
attribute [local simp] Mpfx.Dyadic.coe_real_inj


section
namespace Mpfx
private theorem RoundsFinite.nearest_of_trivial {F₁ : FiniteFormat} {tb : TieBreak}
    (hF₁_triv : ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0)
    {x : ℝ} {w' : Dyadic} (hw : w' ∈ F₁) :
    RoundsFinite F₁ (.nearest tb) x w' := by
  have hw'_zero : (w' : ℝ) = 0 := hF₁_triv w' hw
  have h_eq_w' : ∀ z : Dyadic, z ∈ F₁ → z = w' := fun z hzF₁ =>
    (Dyadic.coe_real_inj z w').mp (by rw [hF₁_triv z hzF₁, hw'_zero])
  have h_adj : IsFaithfulRound F₁ x w' := by
    rcases lt_or_ge x 0 with hx_neg | hx_nn
    · right
      refine ⟨hw, by rw [hw'_zero]; linarith, ?_⟩
      intro v hvF₁ _
      rw [hF₁_triv v hvF₁, hw'_zero]
    · left
      refine ⟨hw, by rw [hw'_zero]; exact hx_nn, ?_⟩
      intro v hvF₁ _
      rw [hF₁_triv v hvF₁, hw'_zero]
  have h_close : ∀ z : Dyadic, z ∈ F₁ → IsFaithfulRound F₁ x z →
      |x - (w' : ℝ)| ≤ |x - (z : ℝ)| := by
    intro z hzF₁ _
    rw [hF₁_triv z hzF₁, hw'_zero]
  cases tb with
  | toEven =>
    refine ⟨hw, h_adj, h_close, ?_⟩
    rintro ⟨z, hzF₁, _, hz_ne_w', _⟩
    exact (hz_ne_w' (h_eq_w' z hzF₁)).elim
  | awayZero =>
    refine ⟨hw, h_adj, h_close, ?_⟩
    intro z hzF₁ _ hz_ne_w' _
    exact (hz_ne_w' (h_eq_w' z hzF₁)).elim
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat)
    {tb : TieBreak} {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z)
    (hw : RoundsFinite F₁ (.nearest tb) (z : ℝ) w') :
    RoundsFinite F₁ (.nearest tb) x w' := by
  rcases two_le_p_or_trivial_of_extend_two_withBound_subset hsub with hp_F₂ | hF₁_triv
  · exact roundsRTO_RN_finite_of_extend (extend_two_subset_of_withBound_subset hsub) hp_F₂
      hz hw
  · exact RoundsFinite.nearest_of_trivial hF₁_triv hw.1
end Mpfx

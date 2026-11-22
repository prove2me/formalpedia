-- Prove2me | solution 1 for Fpy.DigitBound.Covers.fmt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:47:35.370044+00:00
-- url     : https://prove2.me/submissions/1d4332f4-5ed2-4fd5-9b70-25a88a91427e

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Join
import Theorems.Thm_Fpy_DigitBound_DEnv_Le_trans
import Theorems.Thm_Fpy_DigitBound_AgreeOut_agree
import Theorems.Thm_Fpy_DigitBound_DEnv_Holds_grow
import Theorems.Thm_Fpy_DigitBound_Within_grow
import Theorems.Thm_Fpy_DigitBound_fresh_bounds
import Theorems.Thm_Fpy_DigitBound_fresh_numIn


set_option autoImplicit true
open Fpy Fpy.DigitBound
namespace Fpy.DigitBound
namespace Covers
theorem _root_.solution {D : FormatDomain} {Ψg Ψ : List Con} {n₀ n₁ : ℕ} {X : List Var}
    {Γᵢ : AEnv D} {Δ Δᵢ : DEnv} {x : Var} {F : D.Fmt} {lo hi : EInt}
    (h : Covers n₀ n₁ Ψg Ψ X Γᵢ Δ Δᵢ) (hF : Fresh n₀ n₁ Ψ) (hΔᵢ : Δᵢ.Below n₁)
    (hx : Γᵢ x = some (.fmt F)) (hin : ∀ w ∈ D.γ F, InRange lo hi w) :
    Covers n₀ (n₁ + 2) Ψg (Ψ ++ bounds n₁ (.const lo) (.const hi) trivial trivial) X Γᵢ Δ
      (Δᵢ.update x (.num (.var (n₁ + 1)) (.var n₁) none)) := by
  intro hb ι σ hs hΓ hU
  obtain ⟨ι₁, a₁, hs₁, hσ₁⟩ := h hb ι σ hs hΓ hU
  obtain ⟨v, hv, hd⟩ := hΓ x _ hx
  obtain ⟨hw⟩ := hd
  ·
    obtain ⟨ι₂, a₂, hs₂, hn⟩ := fresh_numIn (n := n₁) (Lo := .const lo) (Hi := .const hi)
      trivial trivial ι₁ _ fun hnan => ((hin _ hw).resolve_left hnan).symm
    have hFb := fresh_bounds n₁ (Lo := .const lo) (Hi := .const hi) trivial trivial
    have hσ₂ := (hσ₁.grow (hb.append hF) hFb a₂.agree hΔᵢ).update x (.num hn)
    rw [Store.update, ← hv, Function.update_eq_self, List.append_assoc] at hσ₂
    exact ⟨ι₂, a₁.trans hF.le (by omega) a₂, (Sat.congr hF.before a₂.agree hs₁).append hs₂, hσ₂⟩
end Covers
end Fpy.DigitBound

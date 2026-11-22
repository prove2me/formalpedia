-- Prove2me | solution 1 for Fpy.DigitBound.eval_solution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:44:19.790117+00:00
-- url     : https://prove2.me/submissions/acc58ebb-7ea7-486f-9a97-959e68422016

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_DigitBound_Sound
import Theorems.Thm_Fpy_DigitBound_DEnv_Holds_grow
import Theorems.Thm_Fpy_DigitBound_Within_grow


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution (hA : A.Sound Φ) {Δ : DEnv} {Γ : AEnv D} {κ : Option SCtx}
    {χ : Option Val} {Ψg Ψ Ψr : List Con} {n₀ n₁ n₂ : ℕ} {e : Expr (fpy decode)} {d : DVal}
    (hd : DEval decode Φ A Δ Γ κ χ Ψg n₀ e d Ψ n₁) (hFr : Fresh n₁ n₂ Ψr) {σ : Store}
    {C : Val} {ι : Asgn} {v : Val} (h : Eval Φ σ C e v) (hbg : Before n₀ Ψg) (hsg : Sat ι Ψg)
    (hΔ : Δ.Below n₀) (hκ : CtxBelow n₀ κ) (hσ : Δ.Holds Ψg ι σ) (hΓ : Γ.Holds σ)
    (hC : ∀ K ∈ κ, K.Admits ι C) (hχ : Admits χ C) :
    ∃ ι', Sat ι' (Ψg ++ Ψ ++ Ψr) ∧ Describes (Ψg ++ Ψ ++ Ψr) ι' d v := by
  obtain ⟨ι₁, a₁, hs₁, hd₁⟩ := eval_sound hA hd h hbg hsg hΔ hκ hσ hΓ hC hχ
  obtain ⟨hb₁, hsat₁⟩ := step hbg hsg (DEval.wf hd).1 a₁ hs₁
  obtain ⟨ι₂, a₂, hs₂⟩ := Sat.extend hFr ι₁
  exact ⟨ι₂, (Sat.congr hb₁ a₂ hsat₁).append hs₂, hd₁.grow hb₁ hFr a₂ ((DEval.wf hd).2 hΔ hκ)⟩
end Fpy.DigitBound

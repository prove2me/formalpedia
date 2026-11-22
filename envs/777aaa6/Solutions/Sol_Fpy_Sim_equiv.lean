-- Prove2me | solution 1 for Fpy.Sim.equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:04:08.040846+00:00
-- url     : https://prove2.me/submissions/56aee9bb-58da-466f-9d90-6e3b37fa10bf

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable (A : Analysis L D) (Φ Φ' : Program L) (X : Set Var)
variable {A Φ Φ' X}
namespace Fpy
namespace Sim
theorem _root_.solution {Γ : AEnv D} {κ : Option Val} {s s₁ s' : Stmt L}
    (h : Sim Φ Φ' X Γ κ s s₁) (h' : Equiv Φ' X Γ κ s₁ s') (hX : ∀ x ∈ X, Γ x = none) :
    Sim Φ Φ' X Γ κ s s' := by
  intro σ σ' C hΓ hσ hκ
  have hΓ' := hΓ.agree hσ hX
  refine ⟨fun o hs => ?_, fun o' hs' => ?_⟩
  · obtain ⟨o₁, hs₁, hag₁⟩ := (h hΓ hσ hκ).1 o hs
    obtain ⟨o', hs', hag⟩ := (h' hΓ' hκ).1 o₁ hs₁
    exact ⟨o', hs', hag₁.trans hag⟩
  · obtain ⟨o₁, hs₁, hag⟩ := (h' hΓ' hκ).2 o' hs'
    obtain ⟨o, hs, hag₁⟩ := (h hΓ hσ hκ).2 o₁ hs₁
    exact ⟨o, hs, hag₁.trans hag⟩
end Sim
end Fpy

-- Prove2me | solution 1 for Fpy.Equiv.of_fwd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:45:52.471464+00:00
-- url     : https://prove2.me/submissions/3e5ca5ab-8358-409f-9be0-b767546a8c45

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
namespace Fpy
namespace Equiv
theorem _root_.solution {Φ : Program L} {X : Set Var} {Γ : AEnv D} {κ : Option Val}
    {s s' : Stmt L}
    (hfwd : ∀ σ C o, Γ.Holds σ → Admits κ C → Exec Φ σ C s o →
      ∃ o', Exec Φ σ C s' o' ∧ o.Agree X o')
    (hrun : ∀ σ C o', Γ.Holds σ → Admits κ C → Exec Φ σ C s' o' → ∃ o, Exec Φ σ C s o) :
    Equiv Φ X Γ κ s s' := fun σ C hΓ hκ =>
  ⟨fun o hs => hfwd σ C o hΓ hκ hs, fun o' hs' => by
    obtain ⟨o, hs⟩ := hrun σ C o' hΓ hκ hs'
    obtain ⟨o₂, hs₂, hag⟩ := hfwd σ C o hΓ hκ hs
    exact ⟨o, hs, Exec.det _ hs₂ hs' ▸ hag⟩⟩
end Equiv
end Fpy

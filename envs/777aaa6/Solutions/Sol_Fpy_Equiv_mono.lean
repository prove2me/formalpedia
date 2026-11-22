-- Prove2me | solution 1 for Fpy.Equiv.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:00:17.098329+00:00
-- url     : https://prove2.me/submissions/3f903d4d-9091-4f37-84a4-a0bff2524881

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
import Theorems.Thm_Fpy_Store_Agree_mono
import Theorems.Thm_Fpy_Outcome_Agree_mono

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
namespace Fpy
namespace Equiv
theorem _root_.solution {Φ : Program L} {X Y : Set Var} {Γ : AEnv D} {κ : Option Val}
    {s s' : Stmt L} (h : Equiv Φ X Γ κ s s') (hXY : X ⊆ Y) : Equiv Φ Y Γ κ s s' :=
  fun _ _ hΓ hκ =>
    ⟨fun o hs => (h hΓ hκ).1 o hs |>.imp fun _ ⟨hs', hag⟩ => ⟨hs', hag.mono hXY⟩,
     fun o' hs' => (h hΓ hκ).2 o' hs' |>.imp fun _ ⟨hs, hag⟩ => ⟨hs, hag.mono hXY⟩⟩
end Equiv
end Fpy

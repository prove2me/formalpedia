-- Prove2me | solution 1 for Fpy.Rw.sim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:01:51.340355+00:00
-- url     : https://prove2.me/submissions/7d99fc41-07be-4b47-944a-c14c065264f1

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable (A : Analysis L D) (Φ Φ' : Program L) (X : Set Var)
variable {A Φ Φ' X}
namespace Fpy
namespace Rw
theorem _root_.solution (hA : A.Sound Φ) {Γ : AEnv D} {κ : Option Val} {s s' : Stmt L}
    (h : Rw A Φ Φ' X Γ κ s s') : Sim Φ Φ' X Γ κ s s' :=
  fun _ _ _ hΓ hσ hκ =>
    ⟨fun _ hs => exec_fwd hA hs hΓ hσ hκ h, fun _ hs => exec_bwd hA hs hΓ hσ hκ h⟩
end Rw
end Fpy

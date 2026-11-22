-- Prove2me | solution 1 for Fpy.AEnv.Holds.mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:32:00.850272+00:00
-- url     : https://prove2.me/submissions/a8719015-de27-4f50-a599-c8bfafa50a5b

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate

set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
namespace Fpy
namespace AEnv.Holds
theorem _root_.solution {Γ : AEnv D} {σ : Store} (hΓ : Γ.Holds σ) :
    ∀ {ys : List Var} {Fs : List D.Fmt} {ns : List Num}, FmtsIn Γ ys Fs →
      List.Forall₂ (fun y n => σ y = some (.num n)) ys ns →
      List.Forall₂ (fun n F => n ∈ D.γ F) ns Fs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons ⟨_, ha, hF⟩ hs, .cons hn hns => by
    obtain ⟨_, hv, hd⟩ := hΓ _ _ ha
    obtain rfl := Option.some.inj (hv.symm.trans hn)
    exact .cons (hF hd.mem_toFmt) (solution hΓ hs hns)
end AEnv.Holds
end Fpy

-- Prove2me | solution 1 for Fpy.run_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:56:27.607947+00:00
-- url     : https://prove2.me/submissions/bea9f8b3-fcf3-4bce-9816-dba00b38213f

import Definitions.Def_Fpy_FormatInference_Defs
import Definitions.Def_Fpy_FormatInference_Sound

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain} {A : Analysis L D} {Φ : Program L}
namespace Fpy
theorem _root_.solution (hA : A.Sound Φ) {f : Fn} {y : Var} {s : Stmt L} {a a' : AVal D}
    {Γ' : AEnv D} (hΦ : Φ f = some (y, s)) (hs : AExec A Φ (.single y a) (some .real) s Γ' a')
    {v v' : Val} (hv : Describes a v) (hrun : Run Φ f v v') : Describes a' v' := by
  obtain ⟨y', s', hΦ', hexec⟩ := hrun
  rw [hΦ] at hΦ'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ')
  exact exec_sound hA hexec (AEnv.holds_single hv) (admits_some _) hs
end Fpy

-- Prove2me | solution 1 for Fpy.Exec.ite_dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:04:05.165871+00:00
-- url     : https://prove2.me/submissions/259f088d-9fc6-406e-a5e9-66b6249032fe

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}
namespace Fpy
namespace Exec
theorem _root_.solution {e : Expr L} {s₁ s₂ : Stmt L} {o : Outcome} {b : Prop} [Decidable b]
    (he : Eval Φ σ C e (.bool (decide b))) (h₁ : b → Exec Φ σ C s₁ o)
    (h₂ : ¬ b → Exec Φ σ C s₂ o) : Exec Φ σ C (.ite e s₁ s₂) o := by
  by_cases hb : b
  · exact .iteTrue (by rwa [decide_eq_true hb] at he) (h₁ hb)
  · exact .iteFalse (by rwa [decide_eq_false hb] at he) (h₂ hb)
end Exec
end Fpy

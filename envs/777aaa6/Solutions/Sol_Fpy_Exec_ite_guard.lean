-- Prove2me | solution 1 for Fpy.Exec.ite_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:52:07.364656+00:00
-- url     : https://prove2.me/submissions/80837a11-ee1b-4ef1-8b89-e8ed28ff04da

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}
namespace Fpy
namespace Exec
theorem _root_.solution {e : Expr L} {s₁ s₂ : Stmt L} {o : Outcome}
    (h : Exec Φ σ C (.ite e s₁ s₂) o) : ∃ b, Eval Φ σ C e (.bool b) := by
  cases h with
  | iteTrue he _ => exact ⟨_, he⟩
  | iteFalse he _ => exact ⟨_, he⟩
end Exec
end Fpy

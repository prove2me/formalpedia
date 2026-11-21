-- Prove2me | solution 1 for Fpy.Exec.seq_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:52:06.887314+00:00
-- url     : https://prove2.me/submissions/e8007b15-28ae-4807-befb-b19e2ebe32ec

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}
namespace Fpy
namespace Exec
theorem _root_.solution {s₁ s₂ : Stmt L} {o : Outcome} (h : Exec Φ σ C (.seq s₁ s₂) o) :
    ∃ o₁, Exec Φ σ C s₁ o₁ := by
  cases h with
  | seqNormal h₁ _ => exact ⟨_, h₁⟩
  | seqRet h₁ => exact ⟨_, h₁⟩
end Exec
end Fpy

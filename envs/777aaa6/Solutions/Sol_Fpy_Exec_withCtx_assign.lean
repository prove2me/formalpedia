-- Prove2me | solution 1 for Fpy.Exec.withCtx_assign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:48:38.697759+00:00
-- url     : https://prove2.me/submissions/5ad74268-fe40-4700-865d-55a75c98dc22

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}
namespace Fpy
namespace Exec
theorem _root_.solution {e e' : Expr L} {y : Var} {o : Outcome}
    (h : Exec Φ σ C (.withCtx e (.assign y e')) o) : ∃ C' v, Eval Φ σ C' e' v := by
  cases h with | withCtx _ _ h => cases h with | assign he => exact ⟨_, _, he⟩
end Exec
end Fpy

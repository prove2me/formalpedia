-- Prove2me | solution 1 for Fpy.eval_var_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:52:06.348402+00:00
-- url     : https://prove2.me/submissions/f0a2049b-807b-4e83-bff7-06bfdc663baf

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}
namespace Fpy
theorem _root_.solution {x : Var} {v : Val} (h : Eval Φ σ C (.var x) v) : σ x = some v := by
  cases h with | var h => exact h
end Fpy

-- Prove2me | solution 1 for Fpy.Eval.num_of_arith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:02:43.290817+00:00
-- url     : https://prove2.me/submissions/95226e84-cfcb-4b2e-b311-5f50cba6108a

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
import Theorems.Thm_Fpy_EvalList_num_of_mem

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}
namespace Fpy
namespace Eval
theorem _root_.solution {op : L.ArithOp} {es : List (Expr L)} {v : Val} {e : Expr L}
    (h : Eval Φ σ C (.arith op es) v) (he : e ∈ es) : ∃ u, Eval Φ σ C e (.num u) := by
  cases h with | arith hl _ _ => exact hl.num_of_mem e he
end Eval
end Fpy

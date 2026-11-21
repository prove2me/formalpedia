-- Prove2me | solution 1 for Fpy.EvalList.length_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:59:05.599848+00:00
-- url     : https://prove2.me/submissions/564083b0-6f3a-4dc8-8604-d1ec9c067f97

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Fpy_Semantics

set_option autoImplicit true
open Fpy
variable {L : Signature}
variable (Φ : Program L)
namespace Fpy
namespace EvalList
theorem _root_.solution {σ : Store} {C : Val} :
    ∀ {es : List (Expr L)} {vs : List Val}, EvalList Φ σ C es vs → es.length = vs.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => congrArg _ (solution hs)
end EvalList
end Fpy

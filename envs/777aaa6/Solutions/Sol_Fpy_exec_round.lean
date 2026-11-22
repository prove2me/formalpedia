-- Prove2me | solution 1 for Fpy.exec_round
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:32:50.705726+00:00
-- url     : https://prove2.me/submissions/15042b85-5bf1-402d-8378-177055dfb707

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower

set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}
namespace Fpy
theorem _root_.solution {σ : Store} {C : Val} {r : Num → Num} {x t : Var} {u : Num}
    (hr : C.rnd (fpy decode) = some r) (ht : σ t = some (.num u)) :
    Exec Φ σ C (.assign x (.arithOp .round [.var t])) (.normal (σ.update x (.num (r u)))) :=
  .assign (.arith (ns := [u]) (.cons (.var ht) .nil) rfl hr)
end Fpy

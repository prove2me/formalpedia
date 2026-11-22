-- Prove2me | solution 1 for Fpy.exec_nanBranch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:38:23.299338+00:00
-- url     : https://prove2.me/submissions/e1cf596e-9c5b-4e6c-a366-53181373cbd3

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
    {s : Stmt (fpy decode)} (ht : σ t = some (.num u))
    (hs : Exec Φ σ C s (.normal (σ.update x (.num (r u))))) (kn : Bool) :
    Exec Φ σ C (nanBranch r kn x t s) (.normal (σ.update x (.num (r u)))) := by
  cases kn
  · exact hs
  · rcases u with y | (_ | _)
    · exact .iteFalse (.exact (.cons (.var ht) .nil) rfl) hs
    · exact .iteFalse (.exact (.cons (.var ht) .nil) rfl) hs
    · exact .iteTrue (.exact (.cons (.var ht) .nil) rfl) (.assign .num)
end Fpy

-- Prove2me | solution 1 for Fpy.eval_numCmp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:38:10.28344+00:00
-- url     : https://prove2.me/submissions/da7632ba-3ddf-4181-b556-c32da400d738

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
theorem _root_.solution {σ : Store} {C : Val} (s : Bool) {e₁ e₂ : Expr (fpy decode)} {u v : Num}
    (h₁ : Eval Φ σ C e₁ (.num u)) (h₂ : Eval Φ σ C e₂ (.num v)) :
    Eval Φ σ C (.exactOp (cmpOp s) [e₁, e₂]) (.bool (numCmp s u v)) := by
  cases s <;> exact .exact (.cons h₁ (.cons h₂ .nil)) rfl
end Fpy

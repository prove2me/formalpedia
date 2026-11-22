-- Prove2me | solution 1 for Fpy.exec_round_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:34:34.272952+00:00
-- url     : https://prove2.me/submissions/6d441693-4363-4646-80fd-fc4bf6f53b76

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
import Theorems.Thm_Fpy_exec_round
import Theorems.Thm_Fpy_Eval_num_of_arith
import Theorems.Thm_Fpy_eval_var_inv


set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}
namespace Fpy
theorem _root_.solution {σ : Store} {C : Val} {r : Num → Num} {x t : Var} {o : Outcome}
    (hr : C.rnd (fpy decode) = some r) (h : Exec Φ σ C (.assign x (.arithOp .round [.var t])) o) :
    ∃ u, σ t = some (.num u) ∧ o = .normal (σ.update x (.num (r u))) := by
  obtain ⟨u, ht⟩ : ∃ u, σ t = some (.num u) := by
    cases h with
    | assign he =>
      obtain ⟨u, hu⟩ := he.num_of_arith (List.mem_singleton_self _)
      exact ⟨u, eval_var_inv hu⟩
  exact ⟨u, ht, Exec.det _ h (exec_round hr ht)⟩
end Fpy

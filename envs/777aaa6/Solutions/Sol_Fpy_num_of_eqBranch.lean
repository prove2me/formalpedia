-- Prove2me | solution 1 for Fpy.num_of_eqBranch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:40:56.811623+00:00
-- url     : https://prove2.me/submissions/bc1221c9-8379-45f8-8fee-b2f3d24c0a3c

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
import Theorems.Thm_Fpy_num_of_eq
import Theorems.Thm_Fpy_Exec_ite_guard


set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}
namespace Fpy
theorem _root_.solution {σ : Store} {C : Val} {k : Bool} {x t : Var} {c d : Num}
    {s : Stmt (fpy decode)} {o : Outcome} (h : Exec Φ σ C (eqBranch k x t c d s) o)
    (hs : ∀ o, Exec Φ σ C s o → ∃ u, σ t = some (.num u)) : ∃ u, σ t = some (.num u) := by
  cases k
  · exact hs o h
  · obtain ⟨_, he⟩ := Exec.ite_guard h
    exact num_of_eq he
end Fpy

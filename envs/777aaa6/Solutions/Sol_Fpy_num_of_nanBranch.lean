-- Prove2me | solution 1 for Fpy.num_of_nanBranch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:40:28.370488+00:00
-- url     : https://prove2.me/submissions/d369673c-83c6-4c97-bc10-d916de9c37ad

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
import Theorems.Thm_Fpy_num_of_isNaN
import Theorems.Thm_Fpy_Exec_ite_guard


set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}
namespace Fpy
theorem _root_.solution {σ : Store} {C : Val} {r : Num → Num} {kn : Bool} {x t : Var}
    {s : Stmt (fpy decode)} {o : Outcome} (h : Exec Φ σ C (nanBranch r kn x t s) o)
    (hs : ∀ o, Exec Φ σ C s o → ∃ u, σ t = some (.num u)) : ∃ u, σ t = some (.num u) := by
  cases kn
  · exact hs o h
  · obtain ⟨_, he⟩ := Exec.ite_guard h
    exact num_of_isNaN he
end Fpy

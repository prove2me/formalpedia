-- Prove2me | Theorems.Thm_Fpy_exec_eqBranch
-- name    : Fpy.exec_eqBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:34:24.72648+00:00
-- url     : https://prove2.me/theorems/777522be-4ec5-404a-83af-21e316ec15ff
-- title:
--   Fpy: exec eq Branch
-- statement:
--   The Fpy construction uses the exec eq Branch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L321-L334
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L321-L334

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.exec_eqBranch {σ : Store} {C : Val} {r : Num → Num} {x t : Var} {u c d : Num}
    {s : Stmt (fpy decode)} (hd : r c = d) (ht : σ t = some (.num u))
    (hs : Exec Φ σ C s (.normal (σ.update x (.num (r u))))) (k : Bool) :
    Exec Φ σ C (eqBranch k x t c d s) (.normal (σ.update x (.num (r u)))) := by sorry

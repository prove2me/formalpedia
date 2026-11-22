-- Prove2me | Theorems.Thm_Fpy_exec_nanBranch
-- name    : Fpy.exec_nanBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:34:50.467587+00:00
-- url     : https://prove2.me/theorems/c0deee78-76c7-4ead-9e75-3b7d152c5595
-- title:
--   Fpy: exec nan Branch
-- statement:
--   The Fpy construction uses the exec nan Branch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L310-L319
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L310-L319

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.exec_nanBranch {σ : Store} {C : Val} {r : Num → Num} {x t : Var} {u : Num}
    {s : Stmt (fpy decode)} (ht : σ t = some (.num u))
    (hs : Exec Φ σ C s (.normal (σ.update x (.num (r u))))) (kn : Bool) :
    Exec Φ σ C (nanBranch r kn x t s) (.normal (σ.update x (.num (r u)))) := by sorry

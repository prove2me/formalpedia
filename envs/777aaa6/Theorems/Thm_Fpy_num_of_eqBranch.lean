-- Prove2me | Theorems.Thm_Fpy_num_of_eqBranch
-- name    : Fpy.num_of_eqBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:34:50.884576+00:00
-- url     : https://prove2.me/theorems/ab0f1307-5cea-40a6-822a-65b50ec0b9ea
-- title:
--   Fpy: num of eq Branch
-- statement:
--   The Fpy construction uses the num of eq Branch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L344-L350
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L344-L350

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.num_of_eqBranch {σ : Store} {C : Val} {k : Bool} {x t : Var} {c d : Num}
    {s : Stmt (fpy decode)} {o : Outcome} (h : Exec Φ σ C (eqBranch k x t c d s) o)
    (hs : ∀ o, Exec Φ σ C s o → ∃ u, σ t = some (.num u)) : ∃ u, σ t = some (.num u) := by sorry

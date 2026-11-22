-- Prove2me | Theorems.Thm_Fpy_num_of_nanBranch
-- name    : Fpy.num_of_nanBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:34:42.329016+00:00
-- url     : https://prove2.me/theorems/7bd13735-ea9b-45d1-b926-576743194175
-- title:
--   Fpy: num of nan Branch
-- statement:
--   The Fpy construction uses the num of nan Branch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L336-L342
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L336-L342

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.num_of_nanBranch {σ : Store} {C : Val} {r : Num → Num} {kn : Bool} {x t : Var}
    {s : Stmt (fpy decode)} {o : Outcome} (h : Exec Φ σ C (nanBranch r kn x t s) o)
    (hs : ∀ o, Exec Φ σ C s o → ∃ u, σ t = some (.num u)) : ∃ u, σ t = some (.num u) := by sorry

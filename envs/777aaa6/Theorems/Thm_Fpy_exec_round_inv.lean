-- Prove2me | Theorems.Thm_Fpy_exec_round_inv
-- name    : Fpy.exec_round_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:32:54.903048+00:00
-- url     : https://prove2.me/theorems/a8f018ae-ba79-4fbc-9f7f-d56b2b121322
-- title:
--   Fpy: exec round inv
-- statement:
--   The Fpy construction uses the exec round inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L243-L251
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L243-L251

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.exec_round_inv {σ : Store} {C : Val} {r : Num → Num} {x t : Var} {o : Outcome}
    (hr : C.rnd (fpy decode) = some r) (h : Exec Φ σ C (.assign x (.arithOp .round [.var t])) o) :
    ∃ u, σ t = some (.num u) ∧ o = .normal (σ.update x (.num (r u))) := by sorry

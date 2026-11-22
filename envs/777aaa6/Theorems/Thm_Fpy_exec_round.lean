-- Prove2me | Theorems.Thm_Fpy_exec_round
-- name    : Fpy.exec_round
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:32:38.284011+00:00
-- url     : https://prove2.me/theorems/75ecf0f7-045c-4988-b60d-d748332fcdbf
-- title:
--   Fpy: exec round
-- statement:
--   The Fpy construction uses the exec round property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L238-L241
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L238-L241

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.exec_round {σ : Store} {C : Val} {r : Num → Num} {x t : Var} {u : Num}
    (hr : C.rnd (fpy decode) = some r) (ht : σ t = some (.num u)) :
    Exec Φ σ C (.assign x (.arithOp .round [.var t])) (.normal (σ.update x (.num (r u)))) := by sorry

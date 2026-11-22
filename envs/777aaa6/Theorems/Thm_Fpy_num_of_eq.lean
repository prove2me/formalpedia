-- Prove2me | Theorems.Thm_Fpy_num_of_eq
-- name    : Fpy.num_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:34:48.202187+00:00
-- url     : https://prove2.me/theorems/3b6a1036-aada-44d2-8ec8-167918f0eb04
-- title:
--   Fpy: num of eq
-- statement:
--   The Fpy construction uses the num of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L281-L288
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L281-L288

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.num_of_eq {σ : Store} {C : Val} {t : Var} {c : Num} {v : Val}
    (h : Eval Φ σ C (.exactOp .eq [.var t, .num c]) v) : ∃ u, σ t = some (.num u) := by sorry

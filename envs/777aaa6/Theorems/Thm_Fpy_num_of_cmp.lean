-- Prove2me | Theorems.Thm_Fpy_num_of_cmp
-- name    : Fpy.num_of_cmp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:34:27.825355+00:00
-- url     : https://prove2.me/theorems/3a40733e-8d50-4dea-a27a-c9d6265e86f0
-- title:
--   Fpy: num of cmp
-- statement:
--   The Fpy construction uses the num of cmp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L290-L297
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L290-L297

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.num_of_cmp {σ : Store} {C : Val} {s : Bool} {t : Var} {c : Num} {v : Val}
    (h : Eval Φ σ C (.exactOp (cmpOp s) [.num c, .var t]) v) : ∃ u, σ t = some (.num u) := by sorry

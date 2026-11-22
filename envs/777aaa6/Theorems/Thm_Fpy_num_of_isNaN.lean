-- Prove2me | Theorems.Thm_Fpy_num_of_isNaN
-- name    : Fpy.num_of_isNaN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:34:29.008497+00:00
-- url     : https://prove2.me/theorems/6cb221a7-5d84-43b3-9013-c96f58f0b687
-- title:
--   Fpy: num of is Na N
-- statement:
--   The Fpy construction uses the num of is Na N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L273-L279
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L273-L279

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.num_of_isNaN {σ : Store} {C : Val} {t : Var} {v : Val}
    (h : Eval Φ σ C (.exactOp .isNaN [.var t]) v) : ∃ u, σ t = some (.num u) := by sorry

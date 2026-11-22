-- Prove2me | Theorems.Thm_Fpy_eval_numCmp
-- name    : Fpy.eval_numCmp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:34:27.844182+00:00
-- url     : https://prove2.me/theorems/8cb86e1f-89a0-4fc8-9e1a-4b36c8bcd073
-- title:
--   Fpy: eval num Cmp
-- statement:
--   The Fpy construction uses the eval num Cmp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L259-L262
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L259-L262

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.eval_numCmp {σ : Store} {C : Val} (s : Bool) {e₁ e₂ : Expr (fpy decode)} {u v : Num}
    (h₁ : Eval Φ σ C e₁ (.num u)) (h₂ : Eval Φ σ C e₂ (.num v)) :
    Eval Φ σ C (.exactOp (cmpOp s) [e₁, e₂]) (.bool (numCmp s u v)) := by sorry

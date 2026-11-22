-- Prove2me | Theorems.Thm_Fpy_le_of_numCmp
-- name    : Fpy.le_of_numCmp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:34:31.455436+00:00
-- url     : https://prove2.me/theorems/de1412b9-d507-460a-a3bd-7417a98d535f
-- title:
--   Fpy: le of num Cmp
-- statement:
--   The Fpy construction uses the le of num Cmp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L264-L271
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L264-L271

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.le_of_numCmp {s : Bool} {a b : ℝ} (h : numCmp s (.finite a) (.finite b) = true) :
    a ≤ b := by sorry

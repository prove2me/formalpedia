-- Prove2me | Theorems.Thm_Fpy_num_canonicalExp
-- name    : Fpy.num_canonicalExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:35:25.739765+00:00
-- url     : https://prove2.me/theorems/f0629bed-71c2-4e72-9646-c5b5a3873acd
-- title:
--   Fpy: num canonical Exp
-- statement:
--   `max(logb(y) + (1 − p), exp)` is `y`'s canonical exponent.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L422-L435
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L422-L435

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.num_canonicalExp {F : FiniteFormat} {p : ℕ} (hp : F.p = p) {y : ℝ} (hy : y ≠ 0) :
    Num.max (Num.add (Num.logb (.finite y)) (.finite (1 - p))) (qexpNum F.exp) =
      .finite (F.canonicalExp y : ℝ) := by sorry

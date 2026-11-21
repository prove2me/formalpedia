-- Prove2me | Theorems.Thm_Mpfx_Format_opNeg_of_negClosed
-- name    : Mpfx.Format.opNeg_of_negClosed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:32:18.745008+00:00
-- url     : https://prove2.me/theorems/96fc8a1a-1b46-436e-823e-31ffba1559a7
-- title:
--   Format: op Neg of neg Closed
-- statement:
--   With negation-closed specials, negation preserves the format (the paper's
--   `format(neg(e)) = format(e)`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L488-L492
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L488-L492

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.opNeg_of_negClosed {F : Format} (hF : F.NegClosed) : opNeg F = F := by sorry

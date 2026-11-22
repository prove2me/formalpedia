-- Prove2me | Theorems.Thm_Fpy_DigitBound_fresh_numIn
-- name    : Fpy.DigitBound.fresh_numIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:16:34.167331+00:00
-- url     : https://prove2.me/theorems/e23bdc2e-9876-4c2d-82d2-e83e05fa8f52
-- title:
--   Digit Bound: fresh num In
-- statement:
--   `w` lies in the fresh interval `[n + 1, n]` once its digits meet the bounds;
--   `n` takes `w`'s most significant digit, which `Lo` may mention.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L307-L337
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L307-L337

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.fresh_numIn {n : ℕ} {Lo Hi : Term} (hLo : Lo.Below (n + 1)) (hHi : Hi.Below n)
    (ι : Asgn) (w : Num)
    (h : w ≠ nan → msbOf w ≤ Hi.eval ι ∧ Lo.eval (Function.update ι n (msbOf w)) ≤ lsbOf w) :
    ∃ ι', AgreeOut n (n + 2) ι ι' ∧ Sat ι' (bounds n Lo Hi hLo hHi) ∧
      NumIn ι' (.var (n + 1)) (.var n) none w := by sorry

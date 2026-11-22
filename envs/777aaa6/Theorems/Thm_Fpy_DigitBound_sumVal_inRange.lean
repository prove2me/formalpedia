-- Prove2me | Theorems.Thm_Fpy_DigitBound_sumVal_inRange
-- name    : Fpy.DigitBound.sumVal_inRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:44:10.237987+00:00
-- url     : https://prove2.me/theorems/388c2163-b5a9-48d6-b36a-b92c6bc539de
-- title:
--   Digit Bound: sum Val in Range
-- statement:
--   **D-Sum**, on values: the sum of `L ≥ 1` values with digits in `[lo, hi]`
--   has digits in `[lo, hi + ⌈log₂ L⌉]`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L49-L118
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L49-L118

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_DigitBound_Sum
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.sumVal_inRange {lo hi : EInt} {us : List Num} (hL : 1 ≤ us.length)
    (hus : ∀ u ∈ us, InRange lo hi u) :
    InRange lo (hi + ((Nat.clog 2 us.length : ℕ) : ℤ)) (sumVal id us) := by sorry

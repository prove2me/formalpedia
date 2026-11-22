-- Prove2me | Theorems.Thm_Fpy_DigitBound_opOK_of
-- name    : Fpy.DigitBound.opOK_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:57.374055+00:00
-- url     : https://prove2.me/theorems/b50ed344-95ea-46e2-aa01-756607ac498f
-- title:
--   Digit Bound: op OK of
-- statement:
--   A row whose interval is fresh, bounded by `Lo` and `Hi` on the operands'
--   endpoints.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L56-L63
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L56-L63

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}

theorem Fpy.DigitBound.opOK_of {op : ArithOp} {Is : List (Term × Term × Option Term)} {n : ℕ} {Lo Hi : Term}
    (hLo : Lo.Below n) (hHi : Hi.Below n)
    (h : ∀ ι ns u, List.Forall₂ (fun (I : Term × Term × Option Term) n => NumIn ι I.1 I.2.1 I.2.2 n)
      Is ns → op.eval ns = some u → u ≠ nan → msbOf u ≤ Hi.eval ι ∧ Lo.eval ι ≤ lsbOf u) :
    OpOK op Is n (n + 2) (bounds n Lo Hi (hLo.mono (Nat.le_succ n)) hHi) (.var (n + 1))
      (.var n) := by sorry

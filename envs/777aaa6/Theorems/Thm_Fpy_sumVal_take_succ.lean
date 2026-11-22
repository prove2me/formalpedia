-- Prove2me | Theorems.Thm_Fpy_sumVal_take_succ
-- name    : Fpy.sumVal_take_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:07:10.209759+00:00
-- url     : https://prove2.me/theorems/778ec27f-7e4a-476e-9322-06264b5af341
-- title:
--   Fpy: sum Val take succ
-- statement:
--   The Fpy construction uses the sum Val take succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Sum.lean#L44-L52
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Sum.lean#L44-L52

import Definitions.Def_Fpy_Semantics
import Definitions.Def_Fpy_Ops
import Definitions.Def_Fpy_Sum
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}

theorem Fpy.sumVal_take_succ (r : Num → Num) {us : List Num} {k : ℕ} (hk : 1 ≤ k)
    (hkL : k < us.length) :
    sumVal r (us.take (k + 1)) = r (Num.add (sumVal r (us.take k)) us[k]) := by sorry

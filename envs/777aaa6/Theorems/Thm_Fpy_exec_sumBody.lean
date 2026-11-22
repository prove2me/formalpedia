-- Prove2me | Theorems.Thm_Fpy_exec_sumBody
-- name    : Fpy.exec_sumBody
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:07:13.626425+00:00
-- url     : https://prove2.me/theorems/bc03eb43-bb2e-4e45-9423-8bb95a7e4a46
-- title:
--   Fpy: exec sum Body
-- statement:
--   `sum` returns `sumVal r` of its argument's elements.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Sum.lean#L144-L148
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Sum.lean#L144-L148

import Definitions.Def_Fpy_Semantics
import Definitions.Def_Fpy_Ops
import Definitions.Def_Fpy_Sum
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}

theorem Fpy.exec_sumBody {C : Val} {r : Num → Num} (hr : C.rnd (fpy decode) = some r)
    {us : List Num} {o : Outcome}
    (h : Exec Φ (Store.single "xs" (.list (us.map .num))) C sumBody o) :
    o = .ret (.num (sumVal r us)) := by sorry

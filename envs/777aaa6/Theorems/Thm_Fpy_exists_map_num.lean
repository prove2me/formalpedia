-- Prove2me | Theorems.Thm_Fpy_exists_map_num
-- name    : Fpy.exists_map_num
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:07:03.023482+00:00
-- url     : https://prove2.me/theorems/6e01dde1-62ac-4bb4-8c60-89c94d60d4cb
-- title:
--   Fpy: exists map num
-- statement:
--   A list of values that are all numbers.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Sum.lean#L31-L37
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Sum.lean#L31-L37

import Definitions.Def_Fpy_Semantics
import Definitions.Def_Fpy_Ops
import Definitions.Def_Fpy_Sum
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}

theorem Fpy.exists_map_num {P : Num → Prop} : ∀ {vs : List Val}, (∀ w ∈ vs, ∃ u, w = .num u ∧ P u) →
    ∃ us : List Num, vs = us.map .num ∧ ∀ u ∈ us, P u
  := by sorry

-- Prove2me | Theorems.Thm_Fpy_sumLoop_run
-- name    : Fpy.sumLoop_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:07:06.897267+00:00
-- url     : https://prove2.me/theorems/d3febc6b-741d-46c9-9c1d-e81b12a56942
-- title:
--   Fpy: sum Loop run
-- statement:
--   The Fpy construction uses the sum Loop run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Sum.lean#L63-L110
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Sum.lean#L63-L110

import Definitions.Def_Fpy_Semantics
import Definitions.Def_Fpy_Ops
import Definitions.Def_Fpy_Sum
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
variable {C : Val} {r : Num → Num} (hr : C.rnd (fpy decode) = some r) (us : List Num)
include hr

theorem Fpy.sumLoop_run : ∀ j k, us.length - k = j → 1 ≤ k → k ≤ us.length →
    Exec Φ (sumStore us (sumVal r (us.take k)) k) C sumLoop
      (.normal (sumStore us (sumVal r us) us.length)) := by sorry

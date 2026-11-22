-- Prove2me | Theorems.Thm_Fpy_ExactOp_aval_sound
-- name    : Fpy.ExactOp.aval_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:29.070003+00:00
-- url     : https://prove2.me/theorems/b1d7c331-a30c-48fc-9e44-3ace71ef1d25
-- title:
--   Exact Op: aval sound
-- statement:
--   The Exact Op construction uses the aval sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L447-L453
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L447-L453

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.ExactOp.aval_sound (c : Ceiling) {op : ExactOp} {as : List (AVal (Fmt.domain c))}
    {vs : List Val} {v : Val} (hop : op.eval vs = some v) : Describes (op.aval c as) v := by sorry

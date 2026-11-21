-- Prove2me | Theorems.Thm_Fpy_Val_isCtx_of_rnd
-- name    : Fpy.Val.isCtx_of_rnd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:41:30.80202+00:00
-- url     : https://prove2.me/theorems/9ce67878-d807-4576-800a-7bca679902bc
-- title:
--   Val: is Ctx of rnd
-- statement:
--   The Val construction uses the is Ctx of rnd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Semantics.lean#L34-L35
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Semantics.lean#L34-L35

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Fpy_Semantics
set_option autoImplicit true
open Fpy
variable {L : Signature}

theorem Fpy.Val.isCtx_of_rnd {C : Val} {r : Num → Num} (h : C.rnd L = some r) : C.IsCtx := by sorry

-- Prove2me | Theorems.Thm_Fpy_Store_Agree_update_fresh
-- name    : Fpy.Store.Agree.update_fresh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:52:52.88852+00:00
-- url     : https://prove2.me/theorems/69cdcc40-1f18-46ad-96dd-1276560b6f8a
-- title:
--   Agree: update fresh
-- statement:
--   Writing a fresh `t` before `x` changes nothing outside `t`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L68-L72
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L68-L72

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {X : Set Var}

theorem Fpy.Store.Agree.update_fresh (σ : Store) {x t : Var} (v w : Val) :
    (σ.update x v).Agree {t} ((σ.update t w).update x v) := by sorry

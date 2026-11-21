-- Prove2me | Theorems.Thm_Fpy_Store_agree_update_of_mem
-- name    : Fpy.Store.agree_update_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:49:22.006315+00:00
-- url     : https://prove2.me/theorems/6d56a27a-596e-46e3-8bac-a951a2bb4e3b
-- title:
--   Store: agree update of mem
-- statement:
--   Writing a variable of `X` changes nothing outside `X`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L75-L77
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L75-L77

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {X : Set Var}

theorem Fpy.Store.agree_update_of_mem (σ : Store) {u : Var} (hu : u ∈ X) (w : Val) :
    σ.Agree X (σ.update u w) := by sorry

-- Prove2me | Theorems.Thm_P2M_Fpy_forall__of_evalList_3c5f4110a7e7
-- name    : P2M_Fpy_forall__of_evalList_3c5f4110a7e7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:32:09.814401+00:00
-- url     : https://prove2.me/theorems/d03988dc-c5d2-4c92-b88c-6081f56b3185
-- title:
--   P2 M Fpy forall  of eval List 3c5f4110a7e7: P2 M Fpy forall  of eval List 3c5f4110a7e7
-- statement:
--   The numbers the variables `ys` hold in `σ`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L48-L51
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L48-L51

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}

theorem P2M_Fpy_forall__of_evalList_3c5f4110a7e7 {σ : Store} {C : Val} {ys : List Var} {ns : List Num}
    (h : EvalList Φ σ C (ys.map .var) (ns.map .num)) :
    List.Forall₂ (fun y n => σ y = some (.num n)) ys ns := by sorry

alias «Fpy».«forall₂_of_evalList» := P2M_Fpy_forall__of_evalList_3c5f4110a7e7

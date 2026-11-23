-- Prove2me | Theorems.Thm_eval_poly_from_components
-- name    : eval_poly_from_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:06:17.446292+00:00
-- url     : https://prove2.me/theorems/3b9d78cb-a141-4144-9b59-23d2984971f7
-- title:
--   eval poly from components: eval poly from components
-- statement:
--   Evaluation of poly_from_components at y is sum P_i(y^m) * y^i
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L1033-L1036
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L1033-L1036

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem eval_poly_from_components {F : Type*} [CommSemiring F] (m : ℕ)
    (P_i : Fin m → Polynomial F) (y : F) :
    (poly_from_components m P_i).eval y = ∑ i : Fin m, (P_i i).eval (y ^ m) * y ^ (i : ℕ) := by sorry

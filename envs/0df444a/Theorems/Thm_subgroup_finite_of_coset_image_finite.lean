-- Prove2me | Theorems.Thm_subgroup_finite_of_coset_image_finite
-- name    : subgroup_finite_of_coset_image_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:54:28.025856+00:00
-- url     : https://prove2.me/theorems/caa6aa8f-840d-4e8a-8234-384b88be88af
-- title:
--   subgroup finite of coset image finite: subgroup finite of coset image finite
-- statement:
--   If the image of a coset a • H under Units.val is finite, then H is finite.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L159-L163
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L159-L163

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem subgroup_finite_of_coset_image_finite {F : Type*} [Field F]
    (H : Subgroup Fˣ) (a : Fˣ)
    (h_finite : Set.Finite (Set.image (fun x : Fˣ ↦ (x : F)) (a • (H : Set Fˣ)))) :
    Set.Finite (H : Set Fˣ) := by sorry

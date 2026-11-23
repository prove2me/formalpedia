-- Prove2me | Theorems.Thm_ncard_coset_image_eq_ncard_subgroup
-- name    : ncard_coset_image_eq_ncard_subgroup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:01:22.931165+00:00
-- url     : https://prove2.me/theorems/aeba8588-c6af-4012-bb58-dc268116c7ee
-- title:
--   ncard coset image eq ncard subgroup: ncard coset image eq ncard subgroup
-- statement:
--   The ncard of a smul coset image under Units.val equals the ncard of the subgroup.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L166-L169
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L166-L169

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem ncard_coset_image_eq_ncard_subgroup {F : Type*} [Field F]
    (H : Subgroup Fˣ) (a : Fˣ) :
    (Set.image (fun x : Fˣ ↦ (x : F)) (a • (H : Set Fˣ))).ncard = (H : Set Fˣ).ncard := by sorry

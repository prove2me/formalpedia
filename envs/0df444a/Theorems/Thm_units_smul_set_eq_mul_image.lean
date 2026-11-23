-- Prove2me | Theorems.Thm_units_smul_set_eq_mul_image
-- name    : units_smul_set_eq_mul_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:03:00.313124+00:00
-- url     : https://prove2.me/theorems/7d57ca84-84b5-47a5-8873-750446869337
-- title:
--   units smul set eq mul image: units smul set eq mul image
-- statement:
--   The smul set a • H equals the left multiplication image for Fˣ.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L183-L185
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L183-L185

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem units_smul_set_eq_mul_image {F : Type*} [Field F] (H : Subgroup Fˣ) (a : Fˣ) :
    a • (H : Set Fˣ) = Set.image (fun x ↦ a * x) (H : Set Fˣ) := by sorry

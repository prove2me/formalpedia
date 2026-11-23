-- Prove2me | Theorems.Thm_ncard_pow_image_smul_coset
-- name    : ncard_pow_image_smul_coset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:56:32.621066+00:00
-- url     : https://prove2.me/theorems/a0d76473-6cd2-4f16-8e56-e0c0b986b42d
-- title:
--   ncard pow image smul coset: ncard pow image smul coset
-- statement:
--   The ncard of the power image of a smul coset equals the ncard of the power image
--   of the subgroup.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L211-L214
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L211-L214

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem ncard_pow_image_smul_coset {F : Type*} [Field F] (H : Subgroup Fˣ) (a : Fˣ) (m : ℕ) :
    (Set.image (fun x ↦ x ^ m) (a • (H : Set Fˣ))).ncard =
    (Set.image (fun x ↦ x ^ m) (H : Set Fˣ)).ncard := by sorry

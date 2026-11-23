-- Prove2me | Theorems.Thm_subgroup_ncard_eq_finset_card
-- name    : subgroup_ncard_eq_finset_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:56:31.564325+00:00
-- url     : https://prove2.me/theorems/c98d5ec9-e14e-4ef1-81e2-c2f0ed3a4deb
-- title:
--   subgroup ncard eq finset card: subgroup ncard eq finset card
-- statement:
--   The ncard of a subgroup H equals the card of a finset D if D is the image of a coset of H.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L203-L207
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L203-L207

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem subgroup_ncard_eq_finset_card {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (H : Subgroup Fˣ) (a : Fˣ)
    (hD : (D : Set F) = (a • (H : Set Fˣ)).image (fun x : Fˣ ↦ (x : F))) :
    (H : Set Fˣ).ncard = D.card := by sorry

-- Prove2me | Theorems.Thm_pow_domain_card_eq_ncard_pow_image
-- name    : pow_domain_card_eq_ncard_pow_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:56:20.996297+00:00
-- url     : https://prove2.me/theorems/7730dcbd-008b-431c-a980-f1d851b12af6
-- title:
--   pow domain card eq ncard pow image: pow domain card eq ncard pow image
-- statement:
--   The cardinality of pow_domain D m equals the ncard of the power image of the coset.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L188-L200
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L188-L200

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem pow_domain_card_eq_ncard_pow_image {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (H : Subgroup Fˣ) (a : Fˣ) (m : ℕ)
    (hD : (D : Set F) = (a • (H : Set Fˣ)).image (fun x : Fˣ ↦ (x : F))) :
    (pow_domain D m).card = (Set.image (fun x : Fˣ ↦ x ^ m) (a • (H : Set Fˣ))).ncard := by sorry

-- Prove2me | Theorems.Thm_ncard_pow_image_mul_coset
-- name    : ncard_pow_image_mul_coset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:00:20.110795+00:00
-- url     : https://prove2.me/theorems/5dd1354b-7077-4191-856a-eb17a08ff73b
-- title:
--   ncard pow image mul coset: ncard pow image mul coset
-- statement:
--   The power image of a left multiplication coset has the same ncard as the power image of
--   the subgroup.
--   Note: requires CommGroup since (a * h)^m = a^m * h^m only holds in commutative groups.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L147-L156
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L147-L156

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem ncard_pow_image_mul_coset {G : Type*} [CommGroup G] (H : Subgroup G) (a : G) (m : ℕ) :
    (Set.image (fun x ↦ x ^ m) (Set.image (fun x ↦ a * x) (H : Set G))).ncard =
    (Set.image (fun x ↦ x ^ m) (H : Set G)).ncard := by sorry

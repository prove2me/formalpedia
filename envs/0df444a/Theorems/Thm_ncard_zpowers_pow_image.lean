-- Prove2me | Theorems.Thm_ncard_zpowers_pow_image
-- name    : ncard_zpowers_pow_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:00:14.583533+00:00
-- url     : https://prove2.me/theorems/4ebfcdc6-0cf0-4084-9ee3-c824a5936bf2
-- title:
--   ncard zpowers pow image: ncard zpowers pow image
-- statement:
--   The ncard of the image of zpowers(g) under x ↦ x^m equals the ncard of zpowers(g^m).
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L128-L133
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L128-L133

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem ncard_zpowers_pow_image {G : Type*} [Group G] (g : G) (m : ℕ) :
    (Set.image (fun x ↦ x ^ m) (Subgroup.zpowers g : Set G)).ncard =
    (Subgroup.zpowers (g ^ m) : Set G).ncard := by sorry

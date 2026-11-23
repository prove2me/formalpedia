-- Prove2me | Theorems.Thm_ncard_zpowers_eq_orderOf
-- name    : ncard_zpowers_eq_orderOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:00:06.925461+00:00
-- url     : https://prove2.me/theorems/fbe3c097-a208-4f6e-8f88-52e5ebe49ec1
-- title:
--   ncard zpowers eq order Of: ncard zpowers eq order Of
-- statement:
--   The ncard of zpowers equals the orderOf the generator.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L122-L125
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L122-L125

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem ncard_zpowers_eq_orderOf {G : Type*} [Group G] (g : G) :
    (Subgroup.zpowers g : Set G).ncard = orderOf g := by sorry

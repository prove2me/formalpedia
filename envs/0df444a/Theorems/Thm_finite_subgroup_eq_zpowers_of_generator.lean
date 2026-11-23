-- Prove2me | Theorems.Thm_finite_subgroup_eq_zpowers_of_generator
-- name    : finite_subgroup_eq_zpowers_of_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:54:14.779521+00:00
-- url     : https://prove2.me/theorems/2d0fa4c3-a871-49a5-865f-d5c0ad1a2c52
-- title:
--   finite subgroup eq zpowers of generator: finite subgroup eq zpowers of generator
-- statement:
--   A finite subgroup of a group equals the zpowers of any of its generators.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L172-L176
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L172-L176

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem finite_subgroup_eq_zpowers_of_generator {G : Type*} [Group G] (H : Subgroup G)
    [Finite H] (g : H) (hg : ∀ x : H, x ∈ Subgroup.zpowers g) :
    H = Subgroup.zpowers (g : G) := by sorry

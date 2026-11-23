-- Prove2me | Theorems.Thm_degree_poly_from_components_lt
-- name    : degree_poly_from_components_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:05:30.888832+00:00
-- url     : https://prove2.me/theorems/24994465-2299-4aa4-a65c-252a7a10544d
-- title:
--   degree poly from components lt: degree poly from components lt
-- statement:
--   The degree of poly_from_components is less than d if the components have degree less than d/m
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L1008-L1030
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L1008-L1030

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem degree_poly_from_components_lt {F : Type*} [Field F] [DecidableEq F]
    (m : ℕ) (d : ℕ) (hm : m > 0)
    (P_i : Fin m → Polynomial F)
    (h_deg : ∀ i, (P_i i).degree < d / m) :
    (poly_from_components m P_i).degree < d := by sorry

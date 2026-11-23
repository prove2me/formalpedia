-- Prove2me | Theorems.Thm_degree_interpolate_lt_m
-- name    : degree_interpolate_lt_m
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:05:04.865289+00:00
-- url     : https://prove2.me/theorems/91c7a78b-b715-41eb-8473-43367dca1f93
-- title:
--   degree interpolate lt m: degree interpolate lt m
-- statement:
--   The degree interpolate lt m construction uses the degree interpolate lt m property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L938-L942
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L938-L942

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem degree_interpolate_lt_m {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ)
    (hm : m > 0) (f : F → F) (z : F) :
    (Lagrange.interpolate (Block D m z) id f).degree < m := by sorry

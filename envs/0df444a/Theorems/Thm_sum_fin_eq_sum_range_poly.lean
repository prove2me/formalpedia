-- Prove2me | Theorems.Thm_sum_fin_eq_sum_range_poly
-- name    : sum_fin_eq_sum_range_poly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:20:55.460796+00:00
-- url     : https://prove2.me/theorems/310ba026-173e-406e-8e42-05a139a7cd1b
-- title:
--   sum fin eq sum range poly: sum fin eq sum range poly
-- statement:
--   The sum fin eq sum range poly construction uses the sum fin eq sum range poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L961-L963
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L961-L963

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem sum_fin_eq_sum_range_poly {R : Type*} [CommSemiring R] (m : ℕ) (c : ℕ → R) (x : R) :
    ∑ i : Fin m, x ^ (i : ℕ) * c i = ∑ i ∈ Finset.range m, c i * x ^ i := by sorry

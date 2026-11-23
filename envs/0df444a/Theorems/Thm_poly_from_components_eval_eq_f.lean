-- Prove2me | Theorems.Thm_poly_from_components_eval_eq_f
-- name    : poly_from_components_eval_eq_f
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:24:10.964644+00:00
-- url     : https://prove2.me/theorems/bbf7b9ef-c056-48ee-9c08-6967c7d35088
-- title:
--   poly from components eval eq f: poly from components eval eq f
-- statement:
--   The poly from components eval eq f construction uses the poly from components eval eq f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L1092-L1101
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L1092-L1101

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem poly_from_components_eval_eq_f {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (m : ℕ) (hm : m > 0)
    (f : F → F) (S : Finset F) (hS : S ⊆ D)
    (P_i : Fin m → Polynomial F)
    (h_agree : ∀ i, ∀ z ∈ pow_domain S m, (P_i i).eval z = folding_component D m f i z) :
    ∀ x ∈ S, (poly_from_components m P_i).eval x = f x := by sorry

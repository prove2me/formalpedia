-- Prove2me | Theorems.Thm_fold_eq_sum_components
-- name    : fold_eq_sum_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:54:11.890297+00:00
-- url     : https://prove2.me/theorems/a03c1fe6-7c0a-4cec-a319-d32fa20c7c80
-- title:
--   fold eq sum components: fold eq sum components
-- statement:
--   The fold eq sum components construction uses the fold eq sum components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L948-L956
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L948-L956

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem fold_eq_sum_components {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ)
    (hm : m > 0) (f : F → F) (alpha : F) (z : F) :
    Fold D m f alpha z = ∑ i : Fin m, (alpha ^ (i : ℕ)) * folding_component D m f i z := by sorry

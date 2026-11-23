-- Prove2me | Theorems.Thm_reconstruction_from_components
-- name    : reconstruction_from_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:54:03.305251+00:00
-- url     : https://prove2.me/theorems/f0c5553b-cdf2-44b9-84cd-f8919228d003
-- title:
--   reconstruction from components: reconstruction from components
-- statement:
--   The reconstruction from components construction uses the reconstruction from components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L1067-L1074
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L1067-L1074

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem reconstruction_from_components {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ)
    (hm : m > 0) (f : F → F) (y : F) (hy : y ∈ D) :
    f y = ∑ i : Fin m, folding_component D m f i (y ^ m) * y ^ (i : ℕ) := by sorry

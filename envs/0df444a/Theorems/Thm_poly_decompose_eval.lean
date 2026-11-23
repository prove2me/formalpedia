-- Prove2me | Theorems.Thm_poly_decompose_eval
-- name    : poly_decompose_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:17:48.668474+00:00
-- url     : https://prove2.me/theorems/b0bb5d01-a8e5-4769-a07c-07abff9f3a73
-- title:
--   poly decompose eval: poly decompose eval
-- statement:
--   Evaluation of the reconstructed polynomial at any point y.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L224-L228
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L224-L228

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
omit [DecidableEq F]

theorem poly_decompose_eval (m : ℕ) (hm : m > 0) (p : Polynomial F) (y : F) :
    p.eval y = ∑ i : Fin m, (poly_decompose m p i).eval (y ^ m) * y ^ (i : ℕ) := by sorry

-- Prove2me | Theorems.Thm_powersGenerator_prob_eq
-- name    : powersGenerator_prob_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:32:22.060039+00:00
-- url     : https://prove2.me/theorems/23947fe8-db64-442b-b711-21d68b5ced5e
-- title:
--   powers Generator prob eq: powers Generator prob eq
-- statement:
--   The powers Generator prob eq construction uses the powers Generator prob eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L319-L356
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L319-L356

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
open scoped Classical

theorem powersGenerator_prob_eq {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    [MeasurableSpace F] [DiscreteMeasurableSpace F] (m : ℕ) (S : Set (Fin m → F)) :
    (@powersGenerator F _ _ (by infer_instance) _ m).toMeasure S =
    (Finset.univ.filter (fun r ↦ (fun i : Fin m ↦ r ^ (i : ℕ)) ∈ S)).card /
      Fintype.card F := by sorry

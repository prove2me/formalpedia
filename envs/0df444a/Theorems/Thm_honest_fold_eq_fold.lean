-- Prove2me | Theorems.Thm_honest_fold_eq_fold
-- name    : honest_fold_eq_fold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:17:07.961809+00:00
-- url     : https://prove2.me/theorems/dab0f0d4-5907-4a10-b35f-fede6b513798
-- title:
--   honest fold eq fold: honest fold eq fold
-- statement:
--   Lemma: Honest fold satisfies the fold check by definition.
--
--   This is essentially a definitional equality, but we state it explicitly
--   for clarity in later proofs.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L132-L136
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L132-L136

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem honest_fold_eq_fold (P : FRIParameters F) (i : Fin P.num_foldings)
    (f : FRI_domain P i → F) (alpha : F) (z : F)
    (hz : z ∈ FRI_domain P (i + 1)) :
    Fold (FRI_domain P i) (P.m i) (extend_by_zero (FRI_domain P i) f) alpha z =
    FRI_honest_fold P i f alpha ⟨z, hz⟩ := by sorry

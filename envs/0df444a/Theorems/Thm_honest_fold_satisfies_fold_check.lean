-- Prove2me | Theorems.Thm_honest_fold_satisfies_fold_check
-- name    : honest_fold_satisfies_fold_check
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:17:30.794204+00:00
-- url     : https://prove2.me/theorems/5d70c06a-a250-43aa-bf28-bd8d5bcc8705
-- title:
--   honest fold satisfies fold check: honest fold satisfies fold check
-- statement:
--   Lemma: Honest fold satisfies the local fold check.
--
--   This states that if we compute f_{i+1} honestly from f_i, then the
--   fold check Fold(f_i, m_i, α_i)(z) = f_{i+1}(z) is satisfied.
--
--   **Proof**: This is true essentially by definition - the honest fold
--   *is* the result of applying the Fold operation.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L377-L382
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L377-L382

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem honest_fold_satisfies_fold_check (P : FRIParameters F) (i : Fin P.num_foldings)
    (f : FRI_domain P i → F) (alpha : F) (z : F)
    (hz : z ∈ FRI_domain P (i + 1)) :
    Fold (FRI_domain P i) (P.m i) (extend_by_zero (FRI_domain P i) f) alpha z =
    extend_by_zero (FRI_domain P (i + 1)) (FRI_honest_fold P i f alpha) z := by sorry

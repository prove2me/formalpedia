-- Prove2me | Theorems.Thm_honest_transcript_all_in_code
-- name    : honest_transcript_all_in_code
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:03:55.196323+00:00
-- url     : https://prove2.me/theorems/62dbe510-b156-4bf9-ab33-62eca259549b
-- title:
--   honest transcript all in code: honest transcript all in code
-- statement:
--   Lemma: All messages in an honest transcript are codewords.
--
--   **Proof sketch**: By induction on i:
--   - Base case (i = 0): f_0 is a codeword by assumption
--   - Inductive case: f_{i+1} = honest_fold(f_i, α_i), and we proved
--     that honest folding preserves codeword property
--
--   The inductive step uses `honest_fold_preserves_code`.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L400-L421
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L400-L421

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem honest_transcript_all_in_code (P : FRIParameters F) (f_0 : P.D_0 → F)
    (h_f0_in_code : f_0 ∈ (FRI_code P 0).carrier)
    (challenges : FRIVerifierChallenges P) :
    ∀ i : Fin (P.num_foldings + 1),
    FRI_honest_messages P f_0 challenges.alpha i ∈ FRI_code P i := by sorry

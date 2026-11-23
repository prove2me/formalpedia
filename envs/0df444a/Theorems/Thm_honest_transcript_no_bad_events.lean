-- Prove2me | Theorems.Thm_honest_transcript_no_bad_events
-- name    : honest_transcript_no_bad_events
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:40:12.749433+00:00
-- url     : https://prove2.me/theorems/e0e59ea3-020a-4e8f-afaf-ddf0d44369e2
-- title:
--   honest transcript no bad events: honest transcript no bad events
-- statement:
--   Corollary: The honest prover never triggers a bad event.
--
--   This connects completeness to the soundness analysis: the bad events
--   defined for soundness (like FRI_BadEvent) never occur when the
--   prover is honest and starts with a valid codeword.
--
--   **Proof sketch**: Bad events characterize when a non-codeword is close
--   to a codeword after folding. But honest folding preserves codewords,
--   so bad events cannot occur.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L601-L620
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L601-L620

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem honest_transcript_no_bad_events
    (P : FRIParameters F)
    (f_0 : P.D_0 → F)
    (bound : ℝ)
    (h_f0_in_code : f_0 ∈ (FRI_code P 0).carrier)
    (challenges : FRIVerifierChallenges P)
    (T : FRITranscript P)
    (h_T : T = FRI_honest_transcript P f_0 challenges)
    (i : Fin P.num_foldings) :
    ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i) := by sorry

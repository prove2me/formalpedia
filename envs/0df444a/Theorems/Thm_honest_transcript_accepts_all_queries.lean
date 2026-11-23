-- Prove2me | Theorems.Thm_honest_transcript_accepts_all_queries
-- name    : honest_transcript_accepts_all_queries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:39:43.15809+00:00
-- url     : https://prove2.me/theorems/6304c7a3-d37b-444b-8eec-d0ced7c2ebed
-- title:
--   honest transcript accepts all queries: honest transcript accepts all queries
-- statement:
--   Corollary: For codewords, the honest prover produces accepting transcripts
--   regardless of the specific query points chosen.
--
--   This shows that completeness holds uniformly over all possible verifier
--   randomness, not just in expectation.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L579-L588
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean#L579-L588

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem honest_transcript_accepts_all_queries
    (P : FRIParameters F)
    (f_0 : P.D_0 → F)
    (h_f0_in_code : f_0 ∈ (FRI_code P 0).carrier)
    (alpha : Fin P.num_foldings → F)
    (s : Fin P.q_rep → P.D_0) :
    let challenges := {alpha := alpha, s := s}
    let T := FRI_honest_transcript P f_0 challenges
    FRI_verifier_accepts P f_0 T := by sorry

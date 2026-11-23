-- Prove2me | Theorems.Thm_prod_remaining_m_dvd_FRI_degree
-- name    : prod_remaining_m_dvd_FRI_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:11:09.608031+00:00
-- url     : https://prove2.me/theorems/66758b2d-3c07-4c79-a3b3-31e3094f7d6d
-- title:
--   prod remaining m dvd FRI degree: prod remaining m dvd FRI degree
-- statement:
--   The prod remaining m dvd FRI degree construction uses the prod remaining m dvd FRI degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L688-L712
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L688-L712

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem prod_remaining_m_dvd_FRI_degree (P : FRIParameters F) (i : ℕ) (hi : i ≤ P.num_foldings) :
    (∏ j : Fin P.num_foldings with i ≤ j.val, P.m j) ∣ FRI_degree P i := by sorry

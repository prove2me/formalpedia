-- Prove2me | Theorems.Thm_m_dvd_FRI_degree
-- name    : m_dvd_FRI_degree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:57:17.908071+00:00
-- url     : https://prove2.me/theorems/5b3e3c99-f90c-4bd9-b39d-a2d4fc592822
-- title:
--   m dvd FRI degree: m dvd FRI degree
-- statement:
--   The m dvd FRI degree construction uses the m dvd FRI degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L717-L719
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L717-L719

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem m_dvd_FRI_degree (P : FRIParameters F) (i : Fin P.num_foldings) :
    P.m i ∣ FRI_degree P i := by sorry

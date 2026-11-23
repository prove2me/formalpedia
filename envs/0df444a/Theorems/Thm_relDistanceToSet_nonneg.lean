-- Prove2me | Theorems.Thm_relDistanceToSet_nonneg
-- name    : relDistanceToSet_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:07:39.081317+00:00
-- url     : https://prove2.me/theorems/6a514e34-faff-4e7f-ae31-a555503c6668
-- title:
--   rel Distance To Set nonneg: rel Distance To Set nonneg
-- statement:
--   The rel Distance To Set nonneg construction uses the rel Distance To Set nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L206-L211
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L206-L211

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem relDistanceToSet_nonneg {D S : Type*} [Fintype D] [DecidableEq S]
    (f : D → S) (C : Set (D → S)) : 0 ≤ relDistanceToSet f C := by sorry

-- Prove2me | Theorems.Thm_uniform_measure_eq_card_div
-- name    : uniform_measure_eq_card_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:08:24.25834+00:00
-- url     : https://prove2.me/theorems/5039fb1d-ee3b-4159-a2b1-0d33c317a362
-- title:
--   uniform measure eq card div: uniform measure eq card div
-- statement:
--   The uniform measure eq card div construction uses the uniform measure eq card div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L385-L388
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L385-L388

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
omit [Field F] [DecidableEq F]

theorem uniform_measure_eq_card_div [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    [Nonempty F] (S : Set F) [DecidablePred (· ∈ S)] :
    (PMF.uniformOfFintype F).toMeasure S = (Finset.univ.filter (· ∈ S)).card / Fintype.card F := by sorry

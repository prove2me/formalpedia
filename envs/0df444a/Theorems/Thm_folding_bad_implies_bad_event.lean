-- Prove2me | Theorems.Thm_folding_bad_implies_bad_event
-- name    : folding_bad_implies_bad_event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:11:42.0528+00:00
-- url     : https://prove2.me/theorems/1b02b757-9f3f-4c00-b9fc-e98071dd0c18
-- title:
--   folding bad implies bad event: folding bad implies bad event
-- statement:
--   The folding bad implies bad event construction uses the folding bad implies bad event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L103-L151
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L103-L151

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem folding_bad_implies_bad_event [Fintype F]
  (D : Finset F) (m : ℕ) (d : ℕ) (hm : m > 0) (f : D → F) (alpha : F) (delta : ℝ)
  (h_bad : Folding_Bad_Event D m d f alpha delta) :
  BadEvent (reedSolomon (pow_domain D m) (d / m)) m
      (folding_components D m (extend_by_zero D f)) delta (fun i ↦ alpha ^ (i : ℕ)) := by sorry

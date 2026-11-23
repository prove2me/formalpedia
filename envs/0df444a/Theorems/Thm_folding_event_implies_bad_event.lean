-- Prove2me | Theorems.Thm_folding_event_implies_bad_event
-- name    : folding_event_implies_bad_event
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:59:52.066984+00:00
-- url     : https://prove2.me/theorems/b7abae10-8d5e-46a9-8459-e8db8cf5f0dd
-- title:
--   folding event implies bad event: folding event implies bad event
-- statement:
--   The folding event implies bad event construction uses the folding event implies bad event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L64-L98
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L64-L98

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem folding_event_implies_bad_event
    (D : Finset F) (m : ℕ) (d : ℕ) (hm : m > 0) (hd : d ≥ m)
    (f : F → F) (delta : ℝ) (r : F)
    (h_event : FoldingBadEvent D m (reedSolomon D d)
      (reedSolomon (pow_domain D m) (d / m)) f delta r) :
    BadEvent (reedSolomon (pow_domain D m) (d / m)) m (folding_components D m f) delta
      (fun i ↦ r ^ (i : ℕ)) := by sorry

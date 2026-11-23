-- Prove2me | Theorems.Thm_relDistance_le_of_agree_on_subset
-- name    : relDistance_le_of_agree_on_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:11:26.346741+00:00
-- url     : https://prove2.me/theorems/36dd5f20-0e5e-4614-9985-d87e35ab02d4
-- title:
--   rel Distance le of agree on subset: rel Distance le of agree on subset
-- statement:
--   If two functions agree on a subset W, then their relative distance is bounded by 1 - |W|/|D|.
--
--   This follows because the functions can only differ on D \ W, so the Hamming distance is at most
--   |D| - |W|, giving relDistance ≤ (|D| - |W|) / |D| = 1 - |W| / |D|.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L68-L92
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L68-L92

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true

theorem relDistance_le_of_agree_on_subset {D S : Type*} [Fintype D] [DecidableEq S]
    (f g : D → S) (W : Finset D) (h : ∀ z ∈ W, f z = g z) :
    relDistance f g ≤ 1 - (W.card : ℝ) / Fintype.card D := by sorry

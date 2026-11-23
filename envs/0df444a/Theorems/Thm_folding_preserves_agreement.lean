-- Prove2me | Theorems.Thm_folding_preserves_agreement
-- name    : folding_preserves_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:11:27.164416+00:00
-- url     : https://prove2.me/theorems/ac3038ae-1ab9-4c5c-a3b3-0af147caf35a
-- title:
--   folding preserves agreement: folding preserves agreement
-- statement:
--   The folding preserves agreement construction uses the folding preserves agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L165-L213
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L165-L213

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem folding_preserves_agreement [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (D : Finset F) (m : ℕ) (d : ℕ)
    (hm : m > 0) (hd : d ≥ m)
    (h_foldable : IsFoldable D m)
    (bound : ℝ) (errorstar : ℕ → ℝ → ℝ)
    (h_mca : MutualCorrelatedAgreement powersGenerator
      (reedSolomon (pow_domain D m) (d / m)) bound errorstar)
    (f : F → F) (delta : ℝ)
    (h_delta_nonneg : 0 ≤ delta) (h_delta_lt : delta < 1 - bound) :
    (PMF.uniformOfFintype F).toMeasure
      {r | FoldingBadEvent D m (reedSolomon D d)
        (reedSolomon (pow_domain D m) (d / m)) f delta r} ≤
      ENNReal.ofReal (errorstar m delta) := by sorry

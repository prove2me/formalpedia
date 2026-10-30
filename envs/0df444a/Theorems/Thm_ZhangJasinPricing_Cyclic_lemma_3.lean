-- Prove2me | Theorems.Thm_ZhangJasinPricing_Cyclic_lemma_3
-- name    : ZhangJasinPricing.Cyclic.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T07:01:34.577996+00:00
-- url     : https://prove2.me/theorems/755566b7-5775-4d60-91c9-ef0ace903ecc
-- title:
--   Lemma 3 — Optimal threshold-regulated policies and a short representative
-- statement:
--   For every customer model, an optimal threshold-regulated cyclic word exists. Moreover, there exists such an optimal word of length at most 2K+M−2. Both existential clauses refer to the full class of words of arbitrary positive length.
--
--   Differences from the source:
--   - encoding: finite ordered prices, nonnegative cohort amounts, and a general probability law → zero-based natural-number indices with explicit bounds, real cohort amounts, and a measurable probability space; reason: the same instances are represented; real amounts also include the uniform demands used on p. 28
--   - reading: Definition 1 mixes a strict maximum set with a non-strict empty-set test → the maximum and fallback use the displayed strict set; reason: the printed cases leave repeated thresholds undefined; this releases a threshold once reached and retains the larger class (I4)
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, Lemma 3, p. 19 (PDF p. 19)

import Definitions.Def_ZhangJasinPricing_Cyclic_Analysis
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace ZhangJasinPricing.Cyclic
theorem lemma_3 {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) :
    (∃ w, Optimal D .threshold w) ∧
    (∃ w, Optimal D .threshold w ∧ w.length ≤ 2*D.K+D.M-2) := by sorry
end ZhangJasinPricing.Cyclic

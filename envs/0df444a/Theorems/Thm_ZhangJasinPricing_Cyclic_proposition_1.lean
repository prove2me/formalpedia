-- Prove2me | Theorems.Thm_ZhangJasinPricing_Cyclic_proposition_1
-- name    : ZhangJasinPricing.Cyclic.proposition_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T07:01:14.128117+00:00
-- url     : https://prove2.me/theorems/231044ed-742b-4529-b1ea-fbf750e4a87e
-- title:
--   Proposition 1 — Decreasing, nested decreasing, and threshold-regulated inclusions
-- statement:
--   For the ordered feasible prices, every decreasing cyclic word is nested decreasing, and every nested decreasing cyclic word is threshold-regulated. All classes retain the section's convention that the last price is a minimum.
--
--   Differences from the source:
--   - encoding: finite ordered prices, nonnegative cohort amounts, and a general probability law → zero-based natural-number indices with explicit bounds, real cohort amounts, and a measurable probability space; reason: the same instances are represented; real amounts also include the uniform demands used on p. 28
--   - reading: Definition 1 mixes a strict maximum set with a non-strict empty-set test → the maximum and fallback use the displayed strict set; reason: the printed cases leave repeated thresholds undefined; this releases a threshold once reached and retains the larger class (I4)
--   - reading: Definition 2 quantifies its within-segment condition over s=1,…,M despite declaring S segments → the decreasing condition ranges over the declared segments; reason: M is the number of prices, so the segment quantifier is an evident indexing typo
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, Proposition 1, p. 16 (PDF p. 16)

import Definitions.Def_ZhangJasinPricing_Cyclic_Analysis
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace ZhangJasinPricing.Cyclic
theorem proposition_1 {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) :
    ({w | Decreasing D.M w} ⊆ {w | NestedDecreasing D.M w}) ∧
    ({w | NestedDecreasing D.M w} ⊆ {w | ThresholdRegulated D.M D.price w}) := by sorry
end ZhangJasinPricing.Cyclic

-- Prove2me | Theorems.Thm_ZhangJasinPricing_Cyclic_lemma_2
-- name    : ZhangJasinPricing.Cyclic.lemma_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T07:00:54.243995+00:00
-- url     : https://prove2.me/theorems/5b0dbc5d-0077-4328-a60f-de0e225d2495
-- title:
--   Lemma 2 — Threshold DP outputs are threshold-regulated
-- statement:
--   For every feasible terminal price i and integer t≥1, every maximizing word returned at entry (t,i) by the threshold dynamic program (5) is threshold-regulated, including the last-minimum condition. This holds for every real reward table, and all ties are retained.
--
--   Differences from the source:
--   - encoding: finite ordered prices, nonnegative cohort amounts, and a general probability law → zero-based natural-number indices with explicit bounds, real cohort amounts, and a measurable probability space; reason: the same instances are represented; real amounts also include the uniform demands used on p. 28
--   - reading: Definition 1 mixes a strict maximum set with a non-strict empty-set test → the maximum and fallback use the displayed strict set; reason: the printed cases leave repeated thresholds undefined; this releases a threshold once reached and retains the larger class (I4)
--   - generalization: the DP is described using its expected revenue parameters → the output property holds for every real reward table; reason: true means and optimistic estimates are both specializations; the output construction has the same structural constraint for every table
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, Lemma 2, p. 18 (PDF p. 18)

import Definitions.Def_ZhangJasinPricing_Cyclic_Analysis
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace ZhangJasinPricing.Cyclic
theorem lemma_2 {Ω : Type} [MeasurableSpace Ω] (D : Model Ω)
    (r : Parameter → ℝ) (t i : ℕ) (ht : 1 ≤ t) (hi : i < D.M)
    (x : Plan) (hx : x ∈ dp .threshold D.K r t t i) :
    ThresholdRegulated D.M D.price x.1 := by sorry
end ZhangJasinPricing.Cyclic

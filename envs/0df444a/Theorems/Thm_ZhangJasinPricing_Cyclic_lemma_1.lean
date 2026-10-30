-- Prove2me | Theorems.Thm_ZhangJasinPricing_Cyclic_lemma_1
-- name    : ZhangJasinPricing.Cyclic.lemma_1
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T07:01:43.571501+00:00
-- url     : https://prove2.me/theorems/1797c07b-6563-40f1-bba3-7b44e2aec5f4
-- title:
--   Lemma 1 — Optimal decreasing policies: existence and universal length bound
-- statement:
--   For every customer model in §3, an optimal decreasing cyclic policy exists, and every optimal decreasing policy has cycle length at most K+M−1. A static policy has cycle length one as stipulated on p. 11; a nonstatic decreasing word has its full list length. Optimality is attainment of the supremum over all nonempty decreasing words, with no preliminary length restriction.
--
--   Differences from the source:
--   - encoding: finite ordered prices, nonnegative cohort amounts, and a general probability law → zero-based natural-number indices with explicit bounds, real cohort amounts, and a measurable probability space; reason: the same instances are represented; real amounts also include the uniform demands used on p. 28
--   - reading: an optimal decreasing cyclic policy exists and its cycle length cannot be larger than K+M−1, with static policies assigned length one on p. 11 → existence together with a universal bound using decreasingCycleLength, equal to one for constant words and list length otherwise; reason: retains both printed clauses and the explicit static-policy convention; the universal claim still permits tied nonstatic optima (I6)
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, Lemma 1, p. 10 (PDF p. 10)

import Definitions.Def_ZhangJasinPricing_Cyclic_Analysis
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace ZhangJasinPricing.Cyclic
theorem lemma_1 {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) :
    (∃ w, Optimal D .decreasing w) ∧
    (∀ w, Optimal D .decreasing w → decreasingCycleLength w ≤ D.K + D.M - 1) := by sorry
end ZhangJasinPricing.Cyclic

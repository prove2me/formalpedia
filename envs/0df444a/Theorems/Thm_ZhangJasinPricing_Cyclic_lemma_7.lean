-- Prove2me | Theorems.Thm_ZhangJasinPricing_Cyclic_lemma_7
-- name    : ZhangJasinPricing.Cyclic.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T07:01:33.703522+00:00
-- url     : https://prove2.me/theorems/17837b5b-50c0-49dc-bd4a-61ffc4e6afc4
-- title:
--   Lemma 7 — The printed confidence-complement implication
-- statement:
--   Under Assumption 1, at the beginning of an actual OLT episode e with selected word Π′, suppose the complement of the printed event G(e) holds. If every parameter used by Π′ has starting count at least 32 log n(e,c)/ε², where ε>0, then
--
--   $$v^{TR}-\operatorname{averageCycleRevenue}(\Pi')\le\epsilon.$$
--
--   The complement of an intersection of failures is preserved literally. It does not assert simultaneous success of all intervals. The conclusion uses average cycle revenue.
--
--   Differences from the source:
--   - encoding: finite ordered prices, nonnegative cohort amounts, and a general probability law → zero-based natural-number indices with explicit bounds, real cohort amounts, and a measurable probability space; reason: the same instances are represented; real amounts also include the uniform demands used on p. 28
--   - reading: Definition 1 mixes a strict maximum set with a non-strict empty-set test → the maximum and fallback use the displayed strict set; reason: the printed cases leave repeated thresholds undefined; this releases a threshold once reached and retains the larger class (I4)
--   - reading: the p. 9 transition display omits the last waiting cohort → transition experiments follow equation (1), including all previous still-patient cohorts through period ℓ; reason: this is the operational definition on p. 8 and resolves the explicit indexing typo (I3)
--   - reading: Assumption 1 overloads r as a mean and a realization → the ψ₂ bound one applies to revenue realizations and centered errors have finite ψ₂ norm; reason: the text says norm of all r; the informal tail display is not a separate MGF normalization
--   - reading: initialization tests every parameter, with a suggested reset/high/drop procedure → any finite covering list of prescribed test blocks, with incidental high-price samples, reset observations retained as revenue, and a final reset; reason: this specifies the underdetermined testing and first-episode clearing conventions without favorable estimates or idle delays
--   - encoding: division by ε² in the ε-optimality and sampling bounds → ε>0; reason: this states the domain of the printed denominator
--   - generalization: OLT initialization tests each parameter once (p. 20); OLD says at least once (p. 13) → OLT also permits repeated targeted tests in the finite covering list; reason: choosing each parameter once recovers the printed OLT testing prescription under the declared block/reset reading; no source instance in that prescription is excluded
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, Lemma 7, p. 25 (PDF p. 25)

import Definitions.Def_ZhangJasinPricing_Cyclic_Analysis
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace ZhangJasinPricing.Cyclic
theorem lemma_7 {Ω : Type} [MeasurableSpace Ω] (D : Model Ω)
    (init : Initialization D.M D.K) (tie : TieRule)
    (hA : Assumption1 D) (ω : Ω) (e : ℕ) (ep : Episode)
    (hep : IsEpisode D .threshold init tie ω e ep) (ε : ℝ) (hε : 0 < ε)
    (hG : ¬ allFailures D ep)
    (hq : ∀ a ∈ usedParameters .threshold D.K D.price ep.word,
      32 * Real.log ep.cycleCounter / ε^2 ≤ (ep.counts a : ℝ)) :
    benchmark D .threshold - averageRevenue D ep.word ≤ ε := by sorry
end ZhangJasinPricing.Cyclic

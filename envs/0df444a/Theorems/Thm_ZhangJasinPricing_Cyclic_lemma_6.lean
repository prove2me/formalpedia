-- Prove2me | Theorems.Thm_ZhangJasinPricing_Cyclic_lemma_6
-- name    : ZhangJasinPricing.Cyclic.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T07:01:38.99499+00:00
-- url     : https://prove2.me/theorems/325efe20-3cab-464b-b87c-d378ae28faff
-- title:
--   Lemma 6 — Joint confidence-failure and cycle-count bound
-- statement:
--   Under Assumption 1, fix an OLT initialization whose initial parameter counts are all at most Q, an episode e≥1, and an integer m≥1. Let G(e) be the intersection of all failures of the closed confidence intervals with radii √(8 log n(e,c)/qₐ(e)). Then
--
--   $$\mathbb P[G(e)\cap\{n(e,c)=m\}]\le\frac{2A\max\{Q,2K+M-1\}}{m^3}.$$
--
--   This is joint probability, not conditional probability, and G is an intersection, not a union. No independent-sample premise is added.
--
--   Differences from the source:
--   - encoding: finite ordered prices, nonnegative cohort amounts, and a general probability law → zero-based natural-number indices with explicit bounds, real cohort amounts, and a measurable probability space; reason: the same instances are represented; real amounts also include the uniform demands used on p. 28
--   - reading: Definition 1 mixes a strict maximum set with a non-strict empty-set test → the maximum and fallback use the displayed strict set; reason: the printed cases leave repeated thresholds undefined; this releases a threshold once reached and retains the larger class (I4)
--   - reading: the p. 9 transition display omits the last waiting cohort → transition experiments follow equation (1), including all previous still-patient cohorts through period ℓ; reason: this is the operational definition on p. 8 and resolves the explicit indexing typo (I3)
--   - reading: Assumption 1 overloads r as a mean and a realization → the ψ₂ bound one applies to revenue realizations and centered errors have finite ψ₂ norm; reason: the text says norm of all r; the informal tail display is not a separate MGF normalization
--   - reading: initialization tests every parameter, with a suggested reset/high/drop procedure → any finite covering list of prescribed test blocks, with incidental high-price samples, reset observations retained as revenue, and a final reset; reason: this specifies the underdetermined testing and first-episode clearing conventions without favorable estimates or idle delays
--   - encoding: n(e,c) counts cycles before episode e with the algorithm starting n(c)=1 → one plus completed cycles before the episode; an event for an absent episode is empty; reason: this makes the first-episode convention and episode existence explicit
--   - generalization: OLT initialization tests each parameter once (p. 20); OLD says at least once (p. 13) → OLT also permits repeated targeted tests in the finite covering list; reason: choosing each parameter once recovers the printed OLT testing prescription under the declared block/reset reading; no source instance in that prescription is excluded
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, Lemma 6, p. 24 (PDF p. 24)

import Definitions.Def_ZhangJasinPricing_Cyclic_Analysis
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace ZhangJasinPricing.Cyclic
theorem lemma_6 {Ω : Type} [MeasurableSpace Ω] (D : Model Ω)
    (init : Initialization D.M D.K) (tie : TieRule)
    (hA : Assumption1 D) (Q e m : ℕ) (hQ : initialQ init ≤ Q)
    (he : 1 ≤ e) (hm : 1 ≤ m) :
    D.law (failureAtCycle D init tie e m) ≤ ENNReal.ofReal
      (2 * parameterNumber D.M D.K * max (Q : ℝ) (2*D.K+D.M-1) / (m : ℝ)^3) := by sorry
end ZhangJasinPricing.Cyclic

-- Prove2me | Theorems.Thm_ZhangJasinPricing_Cyclic_lemma_4
-- name    : ZhangJasinPricing.Cyclic.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T07:01:42.898199+00:00
-- url     : https://prove2.me/theorems/f078aeae-0b67-41d1-beed-242321db9faa
-- title:
--   Lemma 4 — Number of OLT episodes by the horizon
-- statement:
--   Under Assumption 1, for every OLT run and horizon T≥2, the total number of episodes begun in the first T periods is at most A log₂ T, where A=M+M(M−1)K/2. The count includes an episode still unfinished at T and counts from the original time origin, including the initialization phase.
--
--   Differences from the source:
--   - encoding: finite ordered prices, nonnegative cohort amounts, and a general probability law → zero-based natural-number indices with explicit bounds, real cohort amounts, and a measurable probability space; reason: the same instances are represented; real amounts also include the uniform demands used on p. 28
--   - reading: Definition 1 mixes a strict maximum set with a non-strict empty-set test → the maximum and fallback use the displayed strict set; reason: the printed cases leave repeated thresholds undefined; this releases a threshold once reached and retains the larger class (I4)
--   - reading: the p. 9 transition display omits the last waiting cohort → transition experiments follow equation (1), including all previous still-patient cohorts through period ℓ; reason: this is the operational definition on p. 8 and resolves the explicit indexing typo (I3)
--   - reading: Assumption 1 overloads r as a mean and a realization → the ψ₂ bound one applies to revenue realizations and centered errors have finite ψ₂ norm; reason: the text says norm of all r; the informal tail display is not a separate MGF normalization
--   - reading: initialization tests every parameter, with a suggested reset/high/drop procedure → any finite covering list of prescribed test blocks, with incidental high-price samples, reset observations retained as revenue, and a final reset; reason: this specifies the underdetermined testing and first-episode clearing conventions without favorable estimates or idle delays
--   - generalization: OLT initialization tests each parameter once (p. 20); OLD says at least once (p. 13) → OLT also permits repeated targeted tests in the finite covering list; reason: choosing each parameter once recovers the printed OLT testing prescription under the declared block/reset reading; no source instance in that prescription is excluded
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, Lemma 4, p. 23 (PDF p. 23)

import Definitions.Def_ZhangJasinPricing_Cyclic_Model
import Definitions.Def_ZhangJasinPricing_Cyclic_Policies
import Definitions.Def_ZhangJasinPricing_Cyclic_DynamicPrograms
import Definitions.Def_ZhangJasinPricing_Cyclic_Learning
import Definitions.Def_ZhangJasinPricing_Cyclic_Analysis
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace ZhangJasinPricing.Cyclic
theorem lemma_4 {Ω : Type} [MeasurableSpace Ω] (D : Model Ω)
    (init : Initialization D.M D.K) (tie : TieRule) (hA : Assumption1 D)
    (T : ℕ) (hT : 2 ≤ T) (ω : Ω) :
    ((run D .threshold init tie ω T).episodes.length : ℝ) ≤
      parameterNumber D.M D.K * (Real.log T / Real.log 2) := by sorry
end ZhangJasinPricing.Cyclic

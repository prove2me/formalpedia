-- Prove2me | Theorems.Thm_ZhangJasinPricing_Cyclic_lemma_5
-- name    : ZhangJasinPricing.Cyclic.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T07:01:55.34101+00:00
-- url     : https://prove2.me/theorems/e060b2c6-e89c-48e3-9295-52068e3e92c3
-- title:
--   Lemma 5 — Periods in undersampled OLT episodes
-- statement:
--   Under Assumption 1, let N be the total number of OLT cycles begun through T≥2, including an incomplete last cycle. If Δ is the least positive gap over the full threshold-regulated class and ε≥Δ with ε>0, then the number of word-playing periods in the first T periods belonging to episodes that begin with some used parameter count below 32 log N/ε² is at most
--
--   $$64A(2K+M-2)\frac{\log N}{\epsilon^2}.$$
--
--   The counters and periods come from the actual run. Initialization and inter-episode clearing are outside these episodes.
--
--   Differences from the source:
--   - encoding: finite ordered prices, nonnegative cohort amounts, and a general probability law → zero-based natural-number indices with explicit bounds, real cohort amounts, and a measurable probability space; reason: the same instances are represented; real amounts also include the uniform demands used on p. 28
--   - reading: Definition 1 mixes a strict maximum set with a non-strict empty-set test → the maximum and fallback use the displayed strict set; reason: the printed cases leave repeated thresholds undefined; this releases a threshold once reached and retains the larger class (I4)
--   - reading: the p. 9 transition display omits the last waiting cohort → transition experiments follow equation (1), including all previous still-patient cohorts through period ℓ; reason: this is the operational definition on p. 8 and resolves the explicit indexing typo (I3)
--   - reading: Assumption 1 overloads r as a mean and a realization → the ψ₂ bound one applies to revenue realizations and centered errors have finite ψ₂ norm; reason: the text says norm of all r; the informal tail display is not a separate MGF normalization
--   - reading: initialization tests every parameter, with a suggested reset/high/drop procedure → any finite covering list of prescribed test blocks, with incidental high-price samples, reset observations retained as revenue, and a final reset; reason: this specifies the underdetermined testing and first-episode clearing conventions without favorable estimates or idle delays
--   - encoding: division by ε² in the ε-optimality and sampling bounds → ε>0; reason: this states the domain of the printed denominator
--   - encoding: Δ denotes a minimum positive gap → Δ satisfies IsLeast on the strictly positive gap set; reason: this conditional lemma names the given gap; the main theorem separately asserts its existence rather than adding it as a model assumption
--   - generalization: OLT initialization tests each parameter once (p. 20); OLD says at least once (p. 13) → OLT also permits repeated targeted tests in the finite covering list; reason: choosing each parameter once recovers the printed OLT testing prescription under the declared block/reset reading; no source instance in that prescription is excluded
--   - encoding: N counts cycles in the first T periods, and the bound uses log N → when T ends during initialization, N=0, the counted periods are zero and Real.log 0=0; reason: this explicitly extends the formula by the empty-period value before any cycle starts; for N≥1 it is the printed expression
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, Lemma 5, p. 23 (PDF p. 23)

import Definitions.Def_ZhangJasinPricing_Cyclic_Model
import Definitions.Def_ZhangJasinPricing_Cyclic_Policies
import Definitions.Def_ZhangJasinPricing_Cyclic_DynamicPrograms
import Definitions.Def_ZhangJasinPricing_Cyclic_Learning
import Definitions.Def_ZhangJasinPricing_Cyclic_Analysis
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace ZhangJasinPricing.Cyclic
theorem lemma_5 {Ω : Type} [MeasurableSpace Ω] (D : Model Ω)
    (init : Initialization D.M D.K) (tie : TieRule) (hA : Assumption1 D)
    (T : ℕ) (hT : 2 ≤ T) (ω : Ω) (ε Δ : ℝ)
    (hgap : IsLeast (positiveGaps D .threshold) Δ) (hε : 0 < ε) (hΔ : Δ ≤ ε) :
    (undersampledPeriods D init tie ω T ε : ℝ) ≤
      64 * parameterNumber D.M D.K * (2*D.K+D.M-2) *
        Real.log (cyclesBegun D .threshold init tie ω T) / ε^2 := by sorry
end ZhangJasinPricing.Cyclic

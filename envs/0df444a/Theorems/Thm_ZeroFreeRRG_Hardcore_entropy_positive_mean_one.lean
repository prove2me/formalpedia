-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_entropy_positive_mean_one
-- name    : ZeroFreeRRG.Hardcore.entropy_positive_mean_one
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:31:37.813946+00:00
-- url     : https://prove2.me/theorems/b637c662-bd7d-47b1-9aee-7e1850ff7985
-- title:
--   Positive entropy for a nonconstant mean-one factor
-- statement:
--   Let $E$ be an integrable, nonnegative almost-everywhere random variable with $\mathbb E E=1$ on a probability space, and suppose $E\log E$ is integrable. If $E\ne1$ with positive probability on the nonnegative set, then
--
--   $$\mathbb E[E\log E]>0.$$
--
--   This strict Jensen step is used for the nonconstant Potts edge factor in the proof of Lemma 4.17.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 31; strict Jensen step.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
/-- A nonconstant nonnegative mean-one factor has positive entropy. -/
theorem entropy_positive_mean_one {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → ℝ) (hE : ∀ᵐ ω ∂μ, 0 ≤ E ω) (hInt : Integrable E μ)
    (hEnt : Integrable (fun ω => xlogx (E ω)) μ) (hmean : (∫ ω, E ω ∂μ) = 1)
    (hpos : 0 < μ {ω | 0 ≤ E ω ∧ E ω ≠ 1}) :
    0 < ∫ ω, xlogx (E ω) ∂μ := by sorry
end ZeroFreeRRG.Hardcore

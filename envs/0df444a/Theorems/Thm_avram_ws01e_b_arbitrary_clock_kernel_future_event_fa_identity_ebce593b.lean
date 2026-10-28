-- Prove2me | Theorems.Thm_avram_ws01e_b_arbitrary_clock_kernel_future_event_fa_identity_ebce593b
-- name    : avram_ws01e_b_arbitrary_clock_kernel_future_event_fa_identity_ebce593b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:39:56.256903+00:00
-- url     : https://prove2.me/theorems/42fe857d-5a68-48aa-82e9-66e370b76dc2
-- title:
--   Random-age clock section with a future-event indicator
-- statement:
--   For any fixed process sample ω, the external-clock section of the joint event K(τ(ω),η) and Y(ω)∈B has Q-measure discount(τ(ω)) times the indicator of Y(ω)∈B. Here τ is a measurable nonnegative random age, Y is a measurable future-path statistic independent of τ, K is a jointly measurable clock kernel, and Q{η: K(a,η)}=discount(a). The proof splits on whether Y(ω) belongs to B.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import Theorems.Thm_AvramDividend_Classical_indepStoppingWeight_futureReward_lintegral_factor
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem avram_ws01e_b_arbitrary_clock_kernel_future_event_fa_identity_ebce593b
    {Ω Θ β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (K : ℝ≥0 → Θ → Prop)
    (hK : MeasurableSet {z : ℝ≥0 × Θ | K z.1 z.2})
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hKernel : ∀ a : ℝ≥0, Q {η : Θ | K a η} = discount a)
    (B : Set β) (hB : MeasurableSet B) 
    (hr : (let reward : β → ℝ≥0∞ := B.indicator (fun _ => 1); Measurable reward))
    (hF : (let reward : β → ℝ≥0∞ := B.indicator (fun _ => 1); Measurable (fun z : Ω × Θ => (τ z.1, z.2))))
    (hs0 : (let reward : β → ℝ≥0∞ := B.indicator (fun _ => 1); MeasurableSet
      {z : Ω × Θ | K (τ z.1) z.2}))
    (hs : (let reward : β → ℝ≥0∞ := B.indicator (fun _ => 1); MeasurableSet
      {z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B}))
    : (let reward : β → ℝ≥0∞ := B.indicator (fun _ => 1); (∀ (ω : Ω), Q (Prod.mk ω ⁻¹'
        {z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B}) =
      discount (τ ω) * reward (Y ω))) := by sorry

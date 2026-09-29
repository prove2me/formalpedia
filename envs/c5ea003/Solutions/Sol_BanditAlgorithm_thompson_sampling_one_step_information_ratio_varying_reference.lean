-- Prove2me | solution 1 for BanditAlgorithm.thompson_sampling_one_step_information_ratio_varying_reference
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T00:40:20.556776+00:00
-- url     : https://prove2.me/submissions/a3bed3a2-1415-4951-994e-0c38faadf15b

import Theorems.Thm_BanditAlgorithm_pinsker_squared_bounded_expectation_difference
import Theorems.Thm_BanditAlgorithm_finite_information_ratio_cauchy_schwarz

open MeasureTheory InformationTheory
open scoped ENNReal BigOperators

namespace BanditAlgorithm

theorem _root_.solution
    {k : ℕ} {Omega : Type} {mOmega : MeasurableSpace Omega}
    (p : Fin k → ℝ) (P M : Fin k → Measure Omega)
    [∀ a, IsProbabilityMeasure (P a)] [∀ a, IsProbabilityMeasure (M a)]
    (reward : Fin k → Omega → ℝ)
    (hreward : ∀ a, Measurable (reward a))
    (hreward0 : ∀ a x, 0 ≤ reward a x)
    (hreward1 : ∀ a x, reward a x ≤ 1)
    (hfinite : ∀ a, klDiv (P a) (M a) ≠ ∞) :
    (∑ a, p a * ((∫ x, reward a x ∂(P a)) - ∫ x, reward a x ∂(M a))) ^ 2 ≤
      ((k : ℝ) / 2) * ∑ a, p a ^ 2 * (klDiv (P a) (M a)).toReal := by
  apply finite_information_ratio_cauchy_schwarz p
    (fun a ↦ (∫ x, reward a x ∂(P a)) - ∫ x, reward a x ∂(M a))
    (fun a ↦ (klDiv (P a) (M a)).toReal)
  intro a
  have h := pinsker_squared_bounded_expectation_difference
    (P a) (M a) (reward a) (hreward a) (hreward0 a) (hreward1 a) (hfinite a)
  convert h using 1 <;> ring

end BanditAlgorithm


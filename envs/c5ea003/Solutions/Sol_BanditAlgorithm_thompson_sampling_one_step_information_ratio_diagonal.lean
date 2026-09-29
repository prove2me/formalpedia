-- Prove2me | solution 1 for BanditAlgorithm.thompson_sampling_one_step_information_ratio_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T23:37:53.446005+00:00
-- url     : https://prove2.me/submissions/c8102ed6-3067-4df5-b82e-2cd69b80a59f

import Theorems.Thm_BanditAlgorithm_pinsker_squared_bounded_expectation_difference
import Theorems.Thm_BanditAlgorithm_finite_information_ratio_cauchy_schwarz

open MeasureTheory InformationTheory
open scoped ENNReal BigOperators

namespace BanditAlgorithm

theorem _root_.solution
    {k : ℕ} {Omega : Type} {mOmega : MeasurableSpace Omega}
    (p : Fin k → ℝ) (P : Fin k → Measure Omega)
    [∀ a, IsProbabilityMeasure (P a)]
    (M : Measure Omega) [IsProbabilityMeasure M]
    (reward : Fin k → Omega → ℝ)
    (hreward : ∀ a, Measurable (reward a))
    (hreward0 : ∀ a x, 0 ≤ reward a x)
    (hreward1 : ∀ a x, reward a x ≤ 1)
    (hfinite : ∀ a, klDiv (P a) M ≠ ∞) :
    (∑ a, p a * ((∫ x, reward a x ∂(P a)) - ∫ x, reward a x ∂M)) ^ 2 ≤
      ((k : ℝ) / 2) * ∑ a, p a ^ 2 * (klDiv (P a) M).toReal := by
  apply finite_information_ratio_cauchy_schwarz p
    (fun a ↦ (∫ x, reward a x ∂(P a)) - ∫ x, reward a x ∂M)
    (fun a ↦ (klDiv (P a) M).toReal)
  intro a
  have h := pinsker_squared_bounded_expectation_difference
    (P a) M (reward a) (hreward a) (hreward0 a) (hreward1 a) (hfinite a)
  convert h using 1 <;> ring

end BanditAlgorithm

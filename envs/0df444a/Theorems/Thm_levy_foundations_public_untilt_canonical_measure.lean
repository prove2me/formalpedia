-- Prove2me | Theorems.Thm_levy_foundations_public_untilt_canonical_measure
-- name    : levy_foundations_public_untilt_canonical_measure
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T13:21:11.687088+00:00
-- url     : https://prove2.me/theorems/df8da285-3ac5-4d2d-8fc8-fba041c82b52
-- title:
--   Untilt a finite canonical semigroup limit to obtain a Lévy measure
-- statement:
--   From any finite limit η of the tilted scaled measures tested against bounded continuous functions vanishing at zero, construct ν by restricting η to the complement of zero and dividing by min(1,x²). This ν has no atom at zero and its truncated second moment is finite. For each bounded continuous f vanishing in a neighbourhood of zero, f/min(1,x²) is bounded continuous, so convergence against η transfers to the un-tilted scaled original semigroup laws. This is the source-exact substantive transformation in LeanLevy ConvolutionSemigroup.exists_levyMeasure, pinned 7e73fd9b.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_untilt_canonical_measure
    (S : ProbabilityTheory.ConvolutionSemigroup)
    (η : Measure ℝ) (hη : IsFiniteMeasure η)
    (t_seq : ℕ → {t : ℝ // 0 < t})
    (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 (0 : ℝ)))
    (hconv : ∀ (f : BoundedContinuousFunction ℝ ℝ), f 0 = 0 →
      Tendsto (fun n => ∫ x, f x ∂(S.tiltedScaledMeasure (t_seq n)))
        atTop (𝓝 (∫ x, f x ∂η))) :
    ∃ ν : Measure ℝ, ProbabilityTheory.IsLevyMeasure ν ∧
      ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun n => (t_seq n).val⁻¹ *
            ∫ x, f x ∂(S.measure (t_seq n) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν)) := by
  sorry

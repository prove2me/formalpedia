-- Prove2me | Theorems.Thm_levy_foundations_public_canonical_tilted_measure
-- name    : levy_foundations_public_canonical_tilted_measure
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T13:19:44.443048+00:00
-- url     : https://prove2.me/theorems/6e26c384-f7ac-4691-84e8-bd9ac4f66049
-- title:
--   Canonical finite tilted measure along a common vanishing semigroup-time sequence
-- statement:
--   For each real convolution semigroup, the finite canonical tilted scaled measures have a subsequence at positive times tending to zero whose integrals converge against every bounded continuous real function vanishing at the origin. This is the exact compactness input to the Lévy-measure untilting theorem and is the public counterpart of LeanLevy ConvolutionSemigroup.exists_canonicalMeasure (pinned source 7e73fd9b, LevyKhintchineProof.lean, around lines 2475 onward). It uses uniform tilted mass and tightness, with Dirac top-up at zero only for normalisation.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_canonical_tilted_measure
    (S : ProbabilityTheory.ConvolutionSemigroup) :
    ∃ (η : Measure ℝ) (_ : IsFiniteMeasure η)
      (t_seq : ℕ → {t : ℝ // 0 < t}),
      Tendsto (fun n => (t_seq n).val) atTop (𝓝 (0 : ℝ)) ∧
      ∀ (f : BoundedContinuousFunction ℝ ℝ), f 0 = 0 →
        Tendsto (fun n => ∫ x, f x ∂(S.tiltedScaledMeasure (t_seq n)))
          atTop (𝓝 (∫ x, f x ∂η)) := by
  sorry

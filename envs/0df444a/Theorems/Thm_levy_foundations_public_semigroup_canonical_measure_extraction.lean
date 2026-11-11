-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_canonical_measure_extraction
-- name    : levy_foundations_public_semigroup_canonical_measure_extraction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:18:31.655124+00:00
-- url     : https://prove2.me/theorems/d3cd6d70-dbd1-4902-bd80-df9f90408e3e
-- title:
--   Canonical finite tilted-measure extraction for a real convolution semigroup
-- statement:
--   From the original convolution semigroup, extract a positive vanishing-time sequence and a finite canonical measure η, such that the tilted scaled measures converge against every bounded continuous function vanishing at zero. This is the source-exact compactness step for extracting the Lévy measure, using uniform tilted mass and tightness.
-- source:
--   Source-exact mathematical lemma ProbabilityTheory.ConvolutionSemigroup.exists_canonicalMeasure in https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean. It is a necessary public child of levy_foundations_public_semigroup_levy_measure_extraction (a407ec20) and hence uniqueness.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_canonical_measure_extraction
    (S : ProbabilityTheory.ConvolutionSemigroup) :
    ∃ (η : Measure ℝ) (_ : IsFiniteMeasure η) (t_seq : ℕ → {t : ℝ // 0 < t}),
      Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) ∧
      ∀ (f : BoundedContinuousFunction ℝ ℝ), f 0 = 0 →
        Tendsto (fun n => ∫ x, f x ∂(S.tiltedScaledMeasure (t_seq n)))
          atTop (𝓝 (∫ x, f x ∂η)) := by
  sorry

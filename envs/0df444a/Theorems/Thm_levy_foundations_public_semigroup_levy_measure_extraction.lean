-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_levy_measure_extraction
-- name    : levy_foundations_public_semigroup_levy_measure_extraction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T11:37:01.8552+00:00
-- url     : https://prove2.me/theorems/a407ec20-f0b2-46a7-a269-5aaad3eb2279
-- title:
--   M5 public Lévy measure and common small-time sequence extraction
-- statement:
--   For every real convolution semigroup, extract a Lévy measure and one sequence of positive times tending to zero so that all bounded continuous real test functions vanishing near zero have scaled integral convergence along that same sequence. This is the exact first stage of source theorem ConvolutionSemigroup.exists_levyMeasure and a necessary public input to M5 joint triplet extraction.
-- source:
--   Source-faithful public interface of LeanLevy LevyKhintchineProof.lean theorem ConvolutionSemigroup.exists_levyMeasure; https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean . Parent levy_foundations_public_semigroup_joint_smalltime_triplet_data e8c8b930-909f-4093-973b-161264070bab; existing source theorem 8e29ceb4 is private Open and cannot be a public parent import.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_levy_measure_extraction
    (S : ProbabilityTheory.ConvolutionSemigroup) :
    ∃ (ν : Measure ℝ), IsLevyMeasure ν ∧
      ∃ (t_seq : ℕ → {t : ℝ // 0 < t}),
        Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) ∧
        (∀ (f : BoundedContinuousFunction ℝ ℝ),
          (∃ r > 0, ∀ x, |x| < r → f x = 0) →
          Tendsto (fun n => (t_seq n).val⁻¹ *
              ∫ x, f x ∂(S.measure (t_seq n) : Measure ℝ))
            atTop (𝓝 (∫ x, f x ∂ν))) := by sorry

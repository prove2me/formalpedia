-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_joint_smalltime_triplet_data
-- name    : levy_foundations_public_semigroup_joint_smalltime_triplet_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:04:09.854544+00:00
-- url     : https://prove2.me/theorems/e8c8b930-909f-4093-973b-161264070bab
-- title:
--   Joint small-time subsequence for drift, variance and jump measure
-- statement:
--   Source-faithful public version of LeanLevy ConvolutionSemigroup.exists_drift_variance_jumpMeasure_along_seq. Extract a Lévy measure, atom-free radius r in (1/2,1], drift and nonnegative second-moment limit along one common sequence of positive times tending to zero, with convergence of all bounded continuous test functions vanishing near the origin. The difficult proof uses diagonal compactness and sub-subsequences, not arbitrary independent limits.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

theorem levy_foundations_public_semigroup_joint_smalltime_triplet_data
    (S : ProbabilityTheory.ConvolutionSemigroup) :
    ∃ (r : ℝ) (b : ℝ) (σ_sq : ℝ≥0) (ν : Measure ℝ),
      ProbabilityTheory.IsLevyMeasure ν ∧
      ∃ (t_seq : ℕ → {t : ℝ // 0 < t}),
        r ∈ Set.Ioc (1 / 2 : ℝ) 1 ∧
        ν {x | |x| = r} = 0 ∧
        Filter.Tendsto (fun n => (t_seq n).val) Filter.atTop (nhds (0 : ℝ)) ∧
        Filter.Tendsto (fun n =>
          (t_seq n).val⁻¹ *
            ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ))
          Filter.atTop (nhds b) ∧
        Filter.Tendsto (fun n =>
          (t_seq n).val⁻¹ *
            ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ))
          Filter.atTop (nhds (σ_sq : ℝ)) ∧
        (∀ f : BoundedContinuousFunction ℝ ℝ,
          (∃ r' > 0, ∀ x, |x| < r' → f x = 0) →
          Filter.Tendsto (fun n =>
            (t_seq n).val⁻¹ *
              ∫ x, f x ∂(S.measure (t_seq n) : Measure ℝ))
            Filter.atTop (nhds (∫ x, f x ∂ν))) := by
  sorry

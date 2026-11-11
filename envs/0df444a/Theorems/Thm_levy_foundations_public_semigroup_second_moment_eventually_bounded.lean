-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_second_moment_eventually_bounded
-- name    : levy_foundations_public_semigroup_second_moment_eventually_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T11:54:29.049344+00:00
-- url     : https://prove2.me/theorems/cec79b22-5f46-4b07-9773-c925a19fc77f
-- title:
--   Eventual boundedness of scaled small-ball quadratic moment along any vanishing semigroup times
-- statement:
--   Uniform boundedness of scaled small-jump quadratic moments for every positive-time sequence tending to zero. This reproduces the exact conclusion of the LeanLevy scaled_second_moment_bounded_along_seq theorem, removing an inaccessible private dependency from the M5 public joint Levy-triplet extraction.
-- source:
--   Original LeanLevy LevyKhintchineProof.lean theorem ConvolutionSemigroup.scaled_second_moment_bounded_along_seq, https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean . Private original Prove2Me theorem f730346c-1a9f-4277-a963-d7ed08816864. Public parent e8c8b930-909f-4093-973b-161264070bab; the second moment bound is required for compact Gaussian variance subsequence.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_second_moment_eventually_bounded
    (S : ProbabilityTheory.ConvolutionSemigroup)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (t_seq n).val⁻¹ *
        ∫ x in ProbabilityTheory.smallSet, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ)
          ≤ C := by sorry

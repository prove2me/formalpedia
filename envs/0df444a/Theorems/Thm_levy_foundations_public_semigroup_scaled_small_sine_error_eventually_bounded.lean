-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_scaled_small_sine_error_eventually_bounded
-- name    : levy_foundations_public_semigroup_scaled_small_sine_error_eventually_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T12:22:11.194431+00:00
-- url     : https://prove2.me/theorems/bb11d230-d5ab-4595-a41f-b86b5f1d45b8
-- title:
--   Eventual bound on the scaled small-ball sine-remainder integral
-- statement:
--   The difference between x and sin(x) is of quadratic order near zero, so its scaled integral over the radius-r ball is eventually bounded by the public semigroup quadratic moment bound. This is the hS part of the original LeanLevy drift_limit proof and a genuine component of the M5 drift eventual boundedness theorem. This publication revision follows authoritative acceptance of the imported second-moment theorem 32791.
-- source:
--   LeanLevy LevyKhintchineProof.lean, ConvolutionSemigroup.drift_limit: hS via abs_sub_sin_le_sq_div_two and scaled second moment, https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean . Parent 0fe64c60-e8fd-49af-b662-5e82d1c7dc5a; existing second moment child cec79b22-5f46-4b07-9773-c925a19fc77f.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_second_moment_eventually_bounded
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_scaled_small_sine_error_eventually_bounded
    (S : ProbabilityTheory.ConvolutionSemigroup)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ᶠ n in atTop,
      |(t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, (x - Real.sin x)
        ∂(S.measure (t_seq n) : Measure ℝ)| ≤ C := by sorry

-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_smallball_variance_bound
-- name    : levy_foundations_public_semigroup_smallball_variance_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:04:12.110953+00:00
-- url     : https://prove2.me/theorems/dd8d1506-07c7-4a8f-a8b6-9145160f879b
-- title:
--   Lévy jump-measure small-ball second moment is bounded by the scaled limit
-- statement:
--   Source-faithful public form of LeanLevy's private smallBall_second_moment_nu_le. Bounded continuous clamped quadratic tests supported away from zero converge under scaled semigroup laws. Exhaust the punctured ball by atom-free annuli and control nonnegative integrals using the given small-time second-moment limit. Conclude that the Lévy measure's small-ball second moment cannot exceed the limiting variance.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

theorem levy_foundations_public_semigroup_smallball_variance_bound
    (S : ProbabilityTheory.ConvolutionSemigroup)
    {r : ℝ} (hr : 0 < r)
    {ν : Measure ℝ} (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}} {σ_sq_r : ℝ}
    (hσ : Filter.Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ))
        Filter.atTop (nhds σ_sq_r))
    (h_jump : ∀ f : BoundedContinuousFunction ℝ ℝ,
        (∃ r' > 0, ∀ x, |x| < r' → f x = 0) →
        Filter.Tendsto (fun k => (t_seq k).val⁻¹ *
          ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          Filter.atTop (nhds (∫ x, f x ∂ν))) :
    ∫ x in {x | |x| < r}, x ^ 2 ∂ν ≤ σ_sq_r := by
  sorry

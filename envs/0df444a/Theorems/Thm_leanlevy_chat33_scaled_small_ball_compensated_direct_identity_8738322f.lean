-- Prove2me | Theorems.Thm_leanlevy_chat33_scaled_small_ball_compensated_direct_identity_8738322f
-- name    : leanlevy_chat33_scaled_small_ball_compensated_direct_identity_8738322f
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:45:36.915839+00:00
-- url     : https://prove2.me/theorems/015c6d5c-12e0-488a-9fae-375d159c3bfe
-- title:
--   Leanlevy chat33 scaled small ball compensated direct: Identity
-- statement:
--   The two expressions in the stated equality coincide under the theorem's explicit assumptions.

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_scaled_smallBall_remainder_tendsto
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_integrableOn_ball
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_sq_integrableOn_ball
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem leanlevy_chat33_scaled_small_ball_compensated_direct_identity_8738322f (S : ConvolutionSemigroup)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}} {σ_sq_r : ℝ}
    (hσ : Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ)) atTop (𝓝 σ_sq_r))
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) 
    (hσ_bdd : ∃ C : ℝ, ∀ k, (t_seq k).val⁻¹ *
      ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ) ≤ C)
    (hquad : Tendsto (fun k => (↑ξ ^ 2 / 2 : ℂ) *
      (↑((t_seq k).val⁻¹ * ∫ x in {x | |x| < r}, x ^ 2
        ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ))
      atTop (𝓝 ((↑ξ ^ 2 / 2 : ℂ) * (↑σ_sq_r : ℂ))))
    : ∀ k, ((t_seq k).val⁻¹ : ℂ) *
      ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I)
        ∂(S.measure (t_seq k) : Measure ℝ) =
      (((t_seq k).val⁻¹ : ℂ) * ∫ x in {x | |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
          ∂(S.measure (t_seq k) : Measure ℝ)) -
      (↑ξ ^ 2 / 2 : ℂ) * (↑((t_seq k).val⁻¹ *
          ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ) := by sorry

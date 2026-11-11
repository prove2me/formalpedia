-- Prove2me | Theorems.Thm_levy_foundations_public_scaled_largeSet_charFun_tendsto
-- name    : levy_foundations_public_scaled_largeSet_charFun_tendsto
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T10:46:37.579003+00:00
-- url     : https://prove2.me/theorems/2cce2688-aa83-4809-8f7f-225b9b5e1ba7
-- title:
--   Public complex large-jump characteristic integral limit from real-valued vague convergence
-- statement:
--   Apply the established real large-set integral convergence theorem to cosine-minus-one and sine, which are bounded and continuous. Euler's identity and finite-restriction integrability split the complex characteristic integral. Compose the real limits with the continuous complex embedding and recombine them.

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Combine bounded real and imaginary large-jump integrals to recover the complex limit. -/
theorem levy_foundations_public_scaled_largeSet_charFun_tendsto (S : ConvolutionSemigroup)
    {ρ : ℝ} (hρ : 0 < ρ) (ξ : ℝ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) (hν_atom : ν {x | |x| = ρ} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => ((t_seq k).val⁻¹ : ℂ) *
        ∫ x in largeSet ρ, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in largeSet ρ, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν)) := by sorry

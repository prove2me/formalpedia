-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_scaled_exponential_real_norm_bound
-- name    : levy_foundations_public_semigroup_scaled_exponential_real_norm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T12:23:33.036458+00:00
-- url     : https://prove2.me/theorems/a6edb6bf-3483-4d05-9361-bafed23de7ed
-- title:
--   Uniform scaled characteristic exponential deficit bounded by exponent norm
-- statement:
--   For a convolution semigroup, its characteristic function has norm at most one and its small-time exponential first-order bound controls t⁻¹ Re(1-exp(tψ(ξ))) by twice the norm of ψ(ξ), uniformly in positive t. This is the hkey stage of LeanLevy scaled_mass_bound_real; combining it with Fourier cosine smoothing controls the mass of jumps bounded away from zero.
-- source:
--   Original LeanLevy LevyKhintchineProof.lean private ConvolutionSemigroup.scaled_mass_bound_real, hkey, https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean . M5 drift parent 0fe64c60-e8fd-49af-b662-5e82d1c7dc5a.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_scaled_exponential_real_norm_bound
    (S : ProbabilityTheory.ConvolutionSemigroup)
    (t : {t : ℝ // 0 < t}) (ξ : ℝ) :
    t.val⁻¹ * (1 - Complex.exp ((t.val : ℂ) * S.exponent ξ)).re ≤
      2 * ‖S.exponent ξ‖ := by sorry

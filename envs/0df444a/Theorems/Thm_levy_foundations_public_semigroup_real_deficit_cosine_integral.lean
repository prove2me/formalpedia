-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_real_deficit_cosine_integral
-- name    : levy_foundations_public_semigroup_real_deficit_cosine_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T12:28:23.4243+00:00
-- url     : https://prove2.me/theorems/fbd7a5fb-609f-4772-85af-5b8931e4021d
-- title:
--   Real semigroup characteristic-function deficit equals cosine integral
-- statement:
--   The semigroup characteristic function equals exp(tψ(ξ)); taking the real part of its unit deficit and commuting the real projection with the integrable characteristic-function integral gives the cosine-deficit integral against μ_t. The source-faithful proof was already compiled as an internal lemma of accepted M5 second-moment candidate 32791. Publishing it supports the remaining Fourier-smoothing proof of the large-set mass bound.
-- source:
--   Accepted M5 candidate 32791 helper levy_foundations_aux_re_one_sub_charFun_eq_integral, corresponding to original LeanLevy LevyKhintchineProof.lean private re_one_sub_charFun_eq_integral, https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean . Parent 0fe64c60-e8fd-49af-b662-5e82d1c7dc5a.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_real_deficit_cosine_integral
    (S : ProbabilityTheory.ConvolutionSemigroup)
    (t : {t : ℝ // 0 < t}) (ξ : ℝ) :
    (1 - Complex.exp ((t.val : ℂ) * S.exponent ξ)).re =
      ∫ x, (1 - Real.cos (ξ * x)) ∂(S.measure t : Measure ℝ) := by sorry

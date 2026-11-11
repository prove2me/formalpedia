-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_scaled_sine_eventually_bounded
-- name    : levy_foundations_public_semigroup_scaled_sine_eventually_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T12:10:45.418722+00:00
-- url     : https://prove2.me/theorems/0f192dec-1198-4f70-8a9e-64653bac7f12
-- title:
--   Eventual bound on the scaled sine integral of a convolution semigroup
-- statement:
--   The scaled sine integral is eventually bounded along every positive semigroup time sequence tending to zero. This is the characteristic-function imaginary-part estimate in the original LeanLevy drift_limit proof. It feeds the public M5 drift eventual bound, alongside large-jump sine and small-ball sine-remainder bounds.
-- source:
--   LeanLevy LevyKhintchineProof.lean, ConvolutionSemigroup.drift_limit: hcf_tend, hIm_tend, hIm_bdd, hIm_eq; https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean . Public M5 parent 0fe64c60-e8fd-49af-b662-5e82d1c7dc5a.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_semigroup_scaled_sine_eventually_bounded
    (S : ProbabilityTheory.ConvolutionSemigroup)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ᶠ n in atTop,
      |(t_seq n).val⁻¹ * ∫ x, Real.sin x ∂(S.measure (t_seq n) : Measure ℝ)| ≤ C := by sorry

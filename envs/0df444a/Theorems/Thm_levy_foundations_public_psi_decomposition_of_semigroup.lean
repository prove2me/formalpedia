-- Prove2me | Theorems.Thm_levy_foundations_public_psi_decomposition_of_semigroup
-- name    : levy_foundations_public_psi_decomposition_of_semigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T09:59:48.130605+00:00
-- url     : https://prove2.me/theorems/c9aeb51b-0fcf-48e5-b0af-b33722624295
-- title:
--   Extract a Lévy–Khintchine triplet from a real convolution semigroup
-- statement:
--   For a continuous characteristic exponent of a real convolution semigroup, construct a drift b, a nonnegative Gaussian variance, and a Lévy measure ν whose compensated Lévy–Khintchine integral equals the exponent at every frequency. Source: LeanLevy/Levy/LevyKhintchineProof.lean psi_decomposition, which obtains raw drift/variance/jump-measure limits along a common small-time sequence and corrects drift and Gaussian variance using the mass of a small spatial ball. The necessary substantive steps are joint subsequence extraction, the second moment bound, and the exponent identity; no finite-activity or first-jump-moment restriction is assumed.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory Complex Filter
open scoped NNReal ENNReal

theorem levy_foundations_public_psi_decomposition_of_semigroup
    (S : ProbabilityTheory.ConvolutionSemigroup) :
    ∃ (b : ℝ) (σ_sq : ℝ≥0) (ν : Measure ℝ),
      ProbabilityTheory.IsLevyMeasure ν ∧
      ∀ ξ : ℝ,
        S.exponent ξ = ↑b * ↑ξ * Complex.I
          - ↑(σ_sq : ℝ) * ↑ξ ^ 2 / 2
          + MeasureTheory.integral ν
              (fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x) := by
  sorry

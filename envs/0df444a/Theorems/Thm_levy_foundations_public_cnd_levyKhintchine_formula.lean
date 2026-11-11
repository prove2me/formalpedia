-- Prove2me | Theorems.Thm_levy_foundations_public_cnd_levyKhintchine_formula
-- name    : levy_foundations_public_cnd_levyKhintchine_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:38:19.665788+00:00
-- url     : https://prove2.me/theorems/14ce9111-d793-4cf7-95de-b5f83438d08d
-- title:
--   Public Lévy–Khintchine formula for continuous Hermitian conditionally negative definite real exponents
-- statement:
--   The central analytic Lévy–Khintchine representation for continuous normalised Hermitian conditionally negative definite functions. The original LeanLevy proof is MIT-licensed, and the imported source-header theorem is currently private. This independently published public theorem permits a source-backed proof and reuse in the public M7 route without accessing private proof dependencies.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory Complex

/-- The analytical Lévy–Khintchine representation in the LeanLevy triplet convention, published for use by public Foundations theorems. -/
theorem levy_foundations_public_cnd_levyKhintchine_formula
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_cnd : ProbabilityTheory.IsConditionallyNegativeDefinite ψ)
    (hψ_herm : ∀ ξ : ℝ, ψ (-ξ) = starRingEnd ℂ (ψ ξ)) :
    ∃ T : ProbabilityTheory.LevyKhintchineTriple, ∀ ξ : ℝ,
      ψ ξ = ↑T.drift * ↑ξ * Complex.I
        - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
        + MeasureTheory.integral T.levyMeasure
            (fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x) := by sorry

-- Prove2me | Theorems.Thm_levy_foundations_cnd_exponent_has_triplet
-- name    : levy_foundations_cnd_exponent_has_triplet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:16:10.85271+00:00
-- url     : https://prove2.me/theorems/6c6832f6-6512-4c21-a4ea-17bef4b44338
-- title:
--   Continuous normalised Hermitian conditionally negative definite functions have a Lévy–Khintchine triplet
-- statement:
--   The integral representation theorem for continuous Hermitian conditionally negative definite functions. Extract the drift, Gaussian variance and Lévy measure using the classical Lévy–Khintchine theorem, and translate its parameters and truncation convention to the Foundations triplet.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent

open MeasureTheory ProbabilityTheory

/-- Lévy–Khintchine representation of a continuous Hermitian conditionally negative definite function in the Foundations triplet representation. -/
theorem levy_foundations_cnd_exponent_has_triplet
    (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hzero : ψ 0 = 0)
    (hherm : ∀ ξ : ℝ, ψ (-ξ) = starRingEnd ℂ (ψ ξ))
    (hcnd : ProbabilityTheory.IsConditionallyNegativeDefinite ψ) :
    ∃ T : LevyFoundations.LevyKhintchineTriple,
      ∀ ξ : ℝ, ψ ξ = LevyFoundations.exponent T ξ := by sorry

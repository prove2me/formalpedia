-- Prove2me | Theorems.Thm_levy_foundations_public_weighted_prokhorov_untilting
-- name    : levy_foundations_public_weighted_prokhorov_untilting
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T13:30:11.526198+00:00
-- url     : https://prove2.me/theorems/39467037-3d09-4b1e-85c2-3284f7679deb
-- title:
--   M5 weighted finite-measure Prokhorov extraction and unweighting
-- statement:
--   Given probability measures μ_n and positive scales a_n whose min(1,x²)-weighted total masses are uniformly bounded and whose scaled mass outside large radii tends uniformly to zero, extract a single subsequence and a Lévy measure ν such that all bounded continuous test functions vanishing near zero have scaled integral convergence. The proof normalises the weighted finite measures by adding missing probability mass at zero, applies Prokhorov, and unweights the weak limit away from zero.
-- source:
--   Mathematically necessary generic compactness/unweighting step of the source LeanLevy Khintchine representation, as described in slink/LeanLevy 7e73fd9b README. Parent public extraction a407ec20-f0b2-46a7-a269-5aaad3eb2279 supplies hMass from Proved second-moment and hTail from uniform largeSet tail and then uses this theorem on shifted t_n=1/(n+1).

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.Prokhorov
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_weighted_prokhorov_untilting
    (μ : ℕ → Measure ℝ) (a : ℕ → ℝ)
    (hprob : ∀ n, IsProbabilityMeasure (μ n))
    (ha : ∀ n, 0 < a n)
    (hMass : ∃ C : ℝ, ∀ n,
      a n * ∫ x, min (1 : ℝ) (x ^ 2) ∂(μ n) ≤ C)
    (hTail : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧
      ∀ n, a n * ((μ n) (largeSet R)).toReal ≤ δ) :
    ∃ ν : Measure ℝ, IsLevyMeasure ν ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ f : BoundedContinuousFunction ℝ ℝ,
          (∃ r > 0, ∀ x, |x| < r → f x = 0) →
          Tendsto (fun n => a (φ n) * ∫ x, f x ∂(μ (φ n)))
            atTop (𝓝 (∫ x, f x ∂ν)) := by sorry

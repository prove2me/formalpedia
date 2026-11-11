-- Prove2me | Theorems.Thm_levy_foundations_public_weighted_prokhorov_compactness
-- name    : levy_foundations_public_weighted_prokhorov_compactness
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T13:44:48.968382+00:00
-- url     : https://prove2.me/theorems/e96edc55-015c-41ce-88f1-0e2e71ec2a94
-- title:
--   M5 weighted weak-limit subsequence for finite tilted measures
-- statement:
--   The uniformly bounded and tight weighted scaled measures admit one common weakly convergent subsequence against every bounded continuous test vanishing at zero. Normalise finite tilted measures into probability measures with a top-up Dirac mass at zero and apply Prokhorov.
-- source:
--   Principal compactness component of the public M5 weighted Prokhorov extraction. It has no dependence on the parent theorem and follows from the uniform weighted total mass and spatial tail estimates.

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.Prokhorov
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_weighted_prokhorov_compactness
    (μ : ℕ → Measure ℝ) (a : ℕ → ℝ)
    (hprob : ∀ n, IsProbabilityMeasure (μ n))
    (ha : ∀ n, 0 < a n)
    (hMass : ∃ C : ℝ, ∀ n,
      a n * ∫ x, min (1 : ℝ) (x ^ 2) ∂(μ n) ≤ C)
    (hTail : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧
      ∀ n, a n * ((μ n) (largeSet R)).toReal ≤ δ) :
    ∃ η : Measure ℝ, IsFiniteMeasure η ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ g : BoundedContinuousFunction ℝ ℝ, g 0 = 0 →
          Tendsto (fun n => a (φ n) *
            ∫ x, min (1 : ℝ) (x ^ 2) * g x ∂(μ (φ n)))
            atTop (𝓝 (∫ x, g x ∂η)) := by sorry

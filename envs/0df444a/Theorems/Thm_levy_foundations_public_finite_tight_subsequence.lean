-- Prove2me | Theorems.Thm_levy_foundations_public_finite_tight_subsequence
-- name    : levy_foundations_public_finite_tight_subsequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:31:32.247823+00:00
-- url     : https://prove2.me/theorems/5ff3cab4-40ba-4af0-9c50-8e50e89fb56a
-- title:
--   Weak subsequential compactness of uniformly bounded tight finite measures
-- statement:
--   A sequence of finite real measures with a common finite total-mass bound and uniform vanishing tails admits a subsequence whose integrals converge against all bounded continuous tests vanishing at zero. The proof normalises to probability measures by adding an atom at zero and invokes Prokhorov compactness; the added atom disappears for the stated test class.
-- source:
--   The source-exact Prokhorov normalisation and atom-top-up argument inside ProbabilityTheory.ConvolutionSemigroup.exists_canonicalMeasure, LeanLevy/Levy/LevyKhintchineProof.lean at original 2512–2665, source commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Generic lemma becomes sole compactness bridge for canonical public child d3cd6d70.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem levy_foundations_public_finite_tight_subsequence
    (ν : ℕ → Measure ℝ) (C : ℝ≥0)
    (hmass : ∀ n, ν n Set.univ ≤ (C : ℝ≥0∞))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ n, ν n (ProbabilityTheory.largeSet R) ≤ ENNReal.ofReal ε) :
    ∃ (η : Measure ℝ), IsFiniteMeasure η ∧
      ∃ (φ : ℕ → ℕ), StrictMono φ ∧
        ∀ (f : BoundedContinuousFunction ℝ ℝ), f 0 = 0 →
          Tendsto (fun k => ∫ x, f x ∂(ν (φ k))) atTop (𝓝 (∫ x, f x ∂η)) := by
  sorry

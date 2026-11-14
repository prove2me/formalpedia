-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_proposition_2_10
-- name    : ZeroFreeRRG.Hardcore.proposition_2_10
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:19:13.971546+00:00
-- url     : https://prove2.me/theorems/f736af7b-6ab2-4d42-9f20-cacb39d2c62c
-- title:
--   Prokhorov compactness for tight sequences
-- statement:
--   Let $(\mu_n)$ be a tight sequence of Borel probability measures on a Polish space. Then some subsequence converges weakly to a Borel probability measure. The space of probability measures carries the weak topology, so its convergence is convergence in distribution. This is Prokhorov’s theorem applied to the laws of the random elements in Proposition 2.10.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Proposition 2.10, printed p. 18.

import Mathlib
open Set Filter MeasureTheory
open scoped Topology

namespace ZeroFreeRRG.Hardcore
theorem proposition_2_10 {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [PolishSpace X] [BorelSpace X] (μ : ℕ → ProbabilityMeasure X)
    (htight : IsTightMeasureSet {((μ n : ProbabilityMeasure X) : Measure X) | n : ℕ}) :
    ∃ ν : ProbabilityMeasure X, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by sorry
end ZeroFreeRRG.Hardcore

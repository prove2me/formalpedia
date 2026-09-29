-- Prove2me | Theorems.Thm_MarkovChainCLT_satisfiesCLT_of_stationary_clt
-- name    : MarkovChainCLT.satisfiesCLT_of_stationary_clt
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T18:04:08.350864+00:00
-- url     : https://prove2.me/theorems/7bf04845-43fc-47e1-ad30-a7f1b0c59037
-- title:
--   Remark 6: a CLT under the stationary start extends to every initial distribution
-- statement:
--   Let $X$ be a Harris ergodic Markov chain with invariant distribution $\pi$ and $f$ measurable. Suppose that **for the stationary start** $X_0 \sim \pi$ we have
--
--   $$\sqrt{n}\,(\bar f_n - E_\pi f) \xrightarrow{d} N(0, v)$$
--
--   for some $v \ge 0$. Then the same holds **for every initial distribution**, i.e. `SatisfiesCLT P π f`.
--
--   This is Remark 6 of the source: "The assumption of stationarity is not an issue for Harris ergodic Markov chains since if a CLT holds for any one initial distribution then it holds for every initial distribution", citing Meyn and Tweedie (1993), Proposition 17.1.6. Harris recurrence is what makes this work: any two initial distributions can be coupled so that the chains meet almost surely in finite time, and a finite random time shift does not affect a $\sqrt n$-normalised limit.
--
--   This is the last step of every corollary in Section 4 of the source, which is why it is worth isolating: the mixing theorems and the martingale-approximation argument alike deliver their conclusion under the stationary start, and this lemma is what converts that into the "for any initial distribution" statement the corollaries assert. Stated with the asymptotic variance already given, so it composes directly with either route.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 4, Remark 6 (arXiv v2 p. 9), citing Meyn & Tweedie (1993), Markov Chains and Stochastic Stability, Proposition 17.1.6.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.satisfiesCLT_of_stationary_clt {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f) (v : ℝ≥0)
    (hclt : TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => chainMeasure P π) (gaussianReal 0 v)) :
    SatisfiesCLT P π f := by sorry

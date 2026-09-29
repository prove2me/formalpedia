-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_boundedInProbability
-- name    : MarkovChainCLT.clt_of_boundedInProbability
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-05T06:55:01.934134+00:00
-- url     : https://prove2.me/theorems/f3241368-ca79-4aaf-88d9-932d89aa5a94
-- title:
--   Chen's theorem: tightness of $\sqrt n\,\bar f_n$ implies the Markov chain CLT
-- statement:
--   Let $X=(X_n)_{n\ge 0}$ be a Markov chain with transition kernel $P$ that is Harris ergodic with invariant probability measure $\pi$, and let $f$ be measurable with $E_\pi f = 0$ and $E_\pi f^2<\infty$. Write $\bar f_n = n^{-1}\sum_{i=1}^{n} f(X_i)$ for the sample average along the chain started from $\pi$.
--
--   If the sequence $\bigl(\sqrt n\,\bar f_n\bigr)_{n\ge 1}$ is bounded in probability, then it satisfies a central limit theorem: there is $\sigma^2\ge 0$ with
--
--   $$\sqrt n\,\bar f_n \xrightarrow{d} N(0,\sigma^2).$$
--
--   This is the substantive half of Chen's characterization (Jones 2004, Theorem 4): mere tightness of the normalized sample averages of a square-integrable functional of a Harris ergodic chain already forces a Gaussian limit. The converse implication — a weakly convergent sequence is bounded in probability — is elementary and is recorded separately.
--
--   **Formalization Note** "Harris ergodic" is encoded by its total-variation characterization: $\pi$ is invariant for $P$ and $\|P^n(x,\cdot)-\pi\|\to 0$ for every starting point $x$. Convergence in distribution is weak convergence of laws under the stationary chain law, and $N(0,0)$ is read as the point mass at $0$, which absorbs the source's "$\sigma_f^2>0$" caveat. The state space is assumed countably generated, the standard general-state-space setting of Meyn and Tweedie.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 4 (arXiv v2 p. 9); original: X. Chen, Limit theorems for functionals of ergodic Markov chains with general state space, Mem. Amer. Math. Soc. 139 (1999), no. 664.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- Chen's theorem, hard direction. -/
theorem MarkovChainCLT.clt_of_boundedInProbability {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (hcent : ∫ x, f x ∂π = 0) (hL2 : MemLp f 2 π)
    (hbdd : BoundedInProbability
      (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * sampleAvg f n ω) (chainMeasure P π)) :
    ∃ v : ℝ≥0, TendstoInDistribution
        (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * sampleAvg f n ω)
        atTop (id : ℝ → ℝ) (fun _ => chainMeasure P π) (gaussianReal 0 v) := by sorry

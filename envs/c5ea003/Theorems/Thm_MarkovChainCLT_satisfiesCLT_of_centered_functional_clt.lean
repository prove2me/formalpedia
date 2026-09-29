-- Prove2me | Theorems.Thm_MarkovChainCLT_satisfiesCLT_of_centered_functional_clt
-- name    : MarkovChainCLT.satisfiesCLT_of_centered_functional_clt
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T15:16:51.192971+00:00
-- url     : https://prove2.me/theorems/45363fa5-3ffd-4192-b307-cbcaf41b804e
-- title:
--   Remark 6: a CLT under the stationary start holds for every initial distribution
-- statement:
--   Let $X$ be a Harris ergodic Markov chain with invariant distribution $\pi$ and let $f \in L^2(\pi)$ be measurable. Write $Y_i = f(X_i) - E_\pi f$ for the centred functional process and $\sigma^2 = E Y_0^2 + 2\sum_{k \ge 1} E(Y_0 Y_k)$ for its asymptotic variance series, both computed under the **stationary** chain. Assume the conclusion delivered by each of the mixing central limit theorems of this mission, namely that the covariance series converges absolutely and that
--
--   $$n^{-1/2} S_n \xrightarrow{d} N(0, \sigma^2) \qquad \text{whenever } \sigma^2 > 0,$$
--
--   where $S_n = \sum_{i<n} Y_i$. Then the chain satisfies the central limit theorem for $f$ in the full sense of eq. (1): there is a single $\sigma_f^2 \ge 0$ such that, **for every initial distribution**,
--
--   $$\sqrt{n}\,(\bar f_n - E_\pi f) \xrightarrow{d} N(0, \sigma_f^2).$$
--
--   Two things are being supplied here. First, the normalisation bookkeeping: $\sqrt{n}(\bar f_n - E_\pi f) = n^{-1/2} S_n$, together with the degenerate case $\sigma^2 = 0$, in which absolute convergence of the covariance series forces $\operatorname{Var}(S_n)/n \to 0$, so $n^{-1/2}S_n \to 0$ in $L^2$ and hence in distribution to the point mass at $0$, which is $N(0,0)$. Second, and substantively, this is **Remark 6** of the source: for a Harris ergodic chain, if a CLT holds for one initial distribution then it holds for every initial distribution (Meyn & Tweedie 1993, Proposition 17.1.6). That is precisely what upgrades the stationary-start statement produced by Theorems 5-8 to the "for any initial distribution" conclusion of Corollaries 1-5.
--
--   This lemma is the shared final step of Jones's proofs of Corollaries 1, 3, 4 and 5, each of which ends with "the result follows from the Theorem and Remark 6".
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 4, Remark 6 (arXiv v2 p. 9) and the proof of Corollary 1 (arXiv v2 p. 10); Remark 6 cites Meyn & Tweedie (1993), Proposition 17.1.6.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.satisfiesCLT_of_centered_functional_clt {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f) (hL2 : MemLp f 2 π)
    (hsum : Summable (fun k : ℕ => ∫ ω, (f (ω 0) - ∫ x, f x ∂π) *
        (f (ω (k + 1)) - ∫ x, f x ∂π) ∂(chainMeasure P π)))
    (hclt : 0 < seqAsymptoticVariance (chainMeasure P π)
          (fun i ω => f (ω i) - ∫ x, f x ∂π) →
        TendstoInDistribution
          (fun (n : ℕ) (ω : ℕ → X) => (Real.sqrt n)⁻¹ *
            ∑ i ∈ Finset.range n, (f (ω i) - ∫ x, f x ∂π))
          atTop (id : ℝ → ℝ) (fun _ => chainMeasure P π)
          (gaussianReal 0 (seqAsymptoticVariance (chainMeasure P π)
            (fun i ω => f (ω i) - ∫ x, f x ∂π)).toNNReal)) :
    SatisfiesCLT P π f := by sorry

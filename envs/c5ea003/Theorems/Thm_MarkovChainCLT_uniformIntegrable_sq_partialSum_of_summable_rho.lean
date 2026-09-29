-- Prove2me | Theorems.Thm_MarkovChainCLT_uniformIntegrable_sq_partialSum_of_summable_rho
-- name    : MarkovChainCLT.uniformIntegrable_sq_partialSum_of_summable_rho
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T07:32:51.734965+00:00
-- url     : https://prove2.me/theorems/015b4d63-f9d2-4aed-9f70-4684cd23210a
-- title:
--   Uniform integrability of $S_n^2/\sigma_n^2$ under summable $\rho$-mixing
-- statement:
--   Let $Y=(Y_n)_{n\ge0}$ be a measurable, centered, strictly stationary real sequence with $Y_0\in L^2$ and summable maximal-correlation coefficients $\sum_{n}\rho(n)<\infty$, whose positive-lag autocovariance series converges, and whose asymptotic variance
--
--   $$\sigma^2=E[Y_0^2]+2\sum_{k\ge1}E[Y_0Y_k]$$
--
--   is strictly positive. Write $S_n=\sum_{i<n}Y_i$ and $\sigma_n^2=E[S_n^2]$. Then the normalized squares are uniformly integrable:
--
--   $$\Bigl\{\frac{S_n^2}{\sigma_n^2} : n\ge 1\Bigr\}\ \text{is uniformly integrable.}$$
--
--   Uniform integrability of the normalized squares is exactly the condition that, by the Cogburn–Denker–Mori–Yoshihara characterization for strongly mixing sequences, is equivalent to the central limit theorem $S_n/\sigma_n\to_d N(0,1)$. Isolating it turns Ibragimov's $\rho$-mixing central limit theorem into a purely moment-theoretic statement: everything else in that theorem is the identification of the limiting variance and the change of normalization from $\sigma_n$ to $\sqrt n$.
--
--   **Formalization Note** Sequences are indexed from $0$, so $S_n=Y_0+\dots+Y_{n-1}$; for the finitely many indices with $\sigma_n=0$ the normalized quantity is read as $0$. Uniform integrability is meant in the $L^1$ sense.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 7 and eq. (12) (Ibragimov's rho-mixing CLT), read through the uniform-integrability characterization of Theorem 3 (arXiv v2 p. 9; R. Cogburn 1960, M. Denker 1986, T. Mori and K. Yoshihara 1986); original: I. A. Ibragimov, Theory of Probability and Its Applications 20 (1975).

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.UniformIntegrable

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.uniformIntegrable_sq_partialSum_of_summable_rho
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hrho : Summable fun n => rhoMixingCoef P Y n)
    (hsum : Summable fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P)
    (hvar : 0 < seqAsymptoticVariance P Y) :
    UniformIntegrable
      (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2
        / ∫ ω', (∑ i ∈ Finset.range n, Y i ω') ^ 2 ∂P) 1 P := by sorry

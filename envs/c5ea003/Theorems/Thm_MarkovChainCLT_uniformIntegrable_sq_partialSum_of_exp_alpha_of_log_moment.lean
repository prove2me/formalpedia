-- Prove2me | Theorems.Thm_MarkovChainCLT_uniformIntegrable_sq_partialSum_of_exp_alpha_of_log_moment
-- name    : MarkovChainCLT.uniformIntegrable_sq_partialSum_of_exp_alpha_of_log_moment
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T08:37:11.692745+00:00
-- url     : https://prove2.me/theorems/646817b7-716d-48fb-bdb9-c0165c85bf41
-- title:
--   Uniform integrability of $S_n^2/\sigma_n^2$ under exponential $\alpha$-mixing and an $E[Y_0^2\log^+|Y_0|]$ moment
-- statement:
--   Let $Y=(Y_n)_{n\ge 0}$ be a measurable, centered, strictly stationary real sequence on a probability space $(\Omega,\mathcal F,P)$ whose strong mixing coefficients decay exponentially,
--
--   $$\alpha(n)\le c\,a^{\,n}\qquad (0\le a<1),$$
--
--   and which satisfies the moment condition $E[Y_0^2\log^+|Y_0|]<\infty$. Assume in addition that the positive-lag autocovariance series $\sum_{k\ge1}E[Y_0Y_{k}]$ converges and that the asymptotic variance
--
--   $$\sigma^2=E[Y_0^2]+2\sum_{k\ge1}E[Y_0Y_k]$$
--
--   is strictly positive. Write $S_n=\sum_{i<n}Y_i$ and $\sigma_n^2=E[S_n^2]$. Then the normalized squares are uniformly integrable:
--
--   $$\Bigl\{\frac{S_n^2}{\sigma_n^2}\;:\;n\ge1\Bigr\}\ \text{is uniformly integrable.}$$
--
--   This is the analytic content of the Doukhan–Massart–Rio central limit theorem. Their theorem is proved by verifying exactly this uniform-integrability condition, which for a strongly mixing centered stationary square-integrable sequence with $\sigma_n^2\to\infty$ is *equivalent* to the central limit theorem $S_n/\sigma_n\to_d N(0,1)$ by the Cogburn–Denker–Mori–Yoshihara characterization (the mission's Theorem 3). Isolating it therefore separates the whole probabilistic difficulty of Jones's Theorem 6 from the two soft steps that surround it: identification of the limiting variance, $\sigma_n^2/n\to\sigma^2$, and the change of normalization from $\sigma_n$ to $\sqrt n$.
--
--   In Doukhan, Massart and Rio the hypothesis is stated in the sharp quantile form $\int_0^1\alpha^{-1}(u)Q^2(u)\,du<\infty$, where $Q$ is the quantile function of $|Y_0|$ and $\alpha^{-1}$ the càdlàg inverse of the mixing-rate function. Under an exponential rate one has $\alpha^{-1}(u)=O(1+\log^+(1/u))$, and the integral condition then reduces to $E[Y_0^2\log^+|Y_0|]<\infty$; the statement above is that special case, which is the form in which Jones quotes the result.
--
--   **Formalization Note** Sequences are indexed from $0$, so $S_n=Y_0+\dots+Y_{n-1}$; for the finitely many indices with $\sigma_n=0$ the normalized quantity is read as $0$ (division by zero). Uniform integrability is meant in the $L^1$ sense. The hypotheses on the autocovariance series and on $\sigma^2$ are carried explicitly, matching the companion statement for $\rho$-mixing sequences.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 6 (arXiv v2 p. 11), read through the uniform-integrability characterization of Theorem 3 (arXiv v2 p. 9; R. Cogburn 1960, M. Denker 1986, T. Mori and K. Yoshihara 1986); original: P. Doukhan, P. Massart and E. Rio, "The functional central limit theorem for strongly mixing processes", Ann. Inst. H. Poincare Probab. Statist. 30 (1994) 63-82, Theorem 1 (uniform integrability of S_n^2/sigma_n^2 under the quantile condition), specialized to an exponential mixing rate.

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.uniformIntegrable_sq_partialSum_of_exp_alpha_of_log_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P)
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    UniformIntegrable
      (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2
        / ∫ ω', (∑ i ∈ Finset.range n, Y i ω') ^ 2 ∂P) 1 P := by sorry

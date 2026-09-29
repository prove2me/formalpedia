-- Prove2me | Theorems.Thm_MarkovChainCLT_uniformIntegrable_sq_partialSum_of_bounded_of_summable_alpha
-- name    : MarkovChainCLT.uniformIntegrable_sq_partialSum_of_bounded_of_summable_alpha
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T12:11:25.118219+00:00
-- url     : https://prove2.me/theorems/0b532951-ae95-469c-b98f-7767a81ed80f
-- title:
--   Uniform integrability of $S_n^2/\sigma_n^2$ for bounded sequences with summable $\alpha$
-- statement:
--   **Uniform integrability of the normalized squared partial sums in the bounded, summably strongly mixing case.**
--
--   Let $Y=(Y_n)_{n\ge 0}$ be a measurable, centered, strictly stationary real sequence on a probability space $(\Omega,\mathcal F,P)$ which is uniformly bounded, $|Y_n| < B$ almost surely for every $n$, and whose strong mixing coefficients are summable, $\sum_{n\ge 0}\alpha(n)<\infty$.  Write
--
--   $$S_n=\sum_{i=0}^{n-1}Y_i,\qquad \sigma_n^2=E[S_n^2],\qquad \sigma^2=E[Y_0^2]+2\sum_{k\ge 1}E[Y_0Y_k],$$
--
--   and assume $\sigma^2>0$.  Then the family
--
--   $$\Bigl\{\,\frac{S_n^2}{\sigma_n^2}\,\Bigr\}_{n\ge 1}$$
--
--   is uniformly integrable.
--
--   **Why this is the remaining content of the bounded-case CLT.**  For a strongly mixing, centered, square-integrable stationary sequence with $\sigma_n^2\to\infty$, the Cogburn–Denker–Mori–Yoshihara criterion (Theorem 3 of the source, `MarkovChainCLT.clt_iff_uniformlyIntegrable_of_alpha_mixing`) states that $S_n/\sigma_n \Rightarrow N(0,1)$ holds *if and only if* $\{S_n^2/\sigma_n^2\}$ is uniformly integrable.  Under the hypotheses above all the surrounding ingredients are available: boundedness gives $Y_0\in L^2$, summability of $\alpha$ gives $\alpha(n)\to 0$ and, through the covariance inequality $|E[Y_0Y_k]|\le 4B^2\alpha(k)$, absolute convergence of the autocovariance series, whence $\sigma_n^2/n\to\sigma^2>0$ and $\sigma_n^2\to\infty$.  So this uniform integrability is exactly what separates the hypotheses of Ibragimov's bounded-case theorem from its conclusion.
--
--   **Remark on the expected proof.**  Uniform integrability here is *not* a consequence of a fourth-moment bound: for bounded sequences the classical estimate $E[S_n^4]=O(n^2)$ needs a quantitative mixing rate such as $\sum_k k^2\alpha(k)<\infty$, which mere summability of $\alpha$ does not provide.  The route intended by the source is Bernstein's big-block/small-block decomposition: with block lengths $p=p(n)$, $q=q(n)$ satisfying $q/p\to 0$, $p/n\to 0$, the small blocks are negligible in $L^2$, and the big blocks decouple up to $16\,k\,\alpha(q)$ by Ibragimov's block-independence estimate, which produces the Gaussian limit and with it — through Theorem 3 read in the other direction, or directly from the block approximation — the uniform integrability asserted here.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, https://arxiv.org/abs/math/0409112, Theorem 5 condition 1 (arXiv v2 p. 9); original result: I. A. Ibragimov, "Some limit theorems for stationary processes", Theory Probab. Appl. 7 (1962) 349-382, and I. A. Ibragimov & Yu. V. Linnik, "Independent and Stationary Sequences of Random Variables" (1971), Ch. 18. The uniform-integrability criterion this statement feeds is Jones 2004, Theorem 3 (Cogburn 1960; Denker 1986; Mori-Yoshihara 1986).

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.UniformIntegrable

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.uniformIntegrable_sq_partialSum_of_bounded_of_summable_alpha
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    UniformIntegrable
      (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2
        / ∫ ω', (∑ i ∈ Finset.range n, Y i ω') ^ 2 ∂P) 1 P := by sorry

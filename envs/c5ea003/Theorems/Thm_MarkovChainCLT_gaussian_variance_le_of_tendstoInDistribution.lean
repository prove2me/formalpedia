-- Prove2me | Theorems.Thm_MarkovChainCLT_gaussian_variance_le_of_tendstoInDistribution
-- name    : MarkovChainCLT.gaussian_variance_le_of_tendstoInDistribution
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T00:55:00.534857+00:00
-- url     : https://prove2.me/theorems/ea46e0de-8e9c-42f4-a79d-812905b57aea
-- title:
--   A uniform second-moment bound is inherited by the Gaussian limit
-- statement:
--   **A uniform second-moment bound passes to the Gaussian limit.** If $Y_n \to N(0,v)$ in distribution and $\mathbb E[Y_n^2] \le B$ for every $n$, then $v \le B$.
--
--   **Why this is not automatic.** Convergence in distribution says nothing about moments: they can jump up in the limit only if mass escapes, and can certainly fail to converge. What *is* true is the lower-semicontinuity direction, $\mathbb E[Y^2] \le \liminf_n \mathbb E[Y_n^2]$, and that is exactly what is needed to transfer a uniform bound to the limit.
--
--   **Where it is used.** In the Markov chain central limit theorem for a square-integrable observable one truncates, proves the theorem for each bounded piece $f_K$ obtaining a limit variance $v_K$, and must then show $(v_K)$ converges. The route goes through the characteristic function, $\int\cos\,dN(0,v_K) = e^{-v_K/2}$, whose Cauchy property transfers back to $v_K$ **only if the $v_K$ stay bounded** — otherwise $e^{-v_K/2}$ could tend to $0$ with $v_K\to\infty$. This lemma supplies exactly that boundedness: the $O(n)$ variance bound for partial sums gives $\mathbb E[(T_n^K)^2] \le 4N\|f_K\|_{L^2(\pi)}^2$ uniformly in $n$, hence $v_K \le 4N\|f_K\|_{L^2(\pi)}^2$.
--
--   **Proof.** Truncate the square: $\varphi_M(x) = \min(x^2, M)$ is bounded and continuous, so convergence in distribution gives $\int\varphi_M\,dN(0,v) = \lim_n \mathbb E[\varphi_M(Y_n)] \le \sup_n\mathbb E[Y_n^2] \le B$, using $\varphi_M \le x^2$. Letting $M\to\infty$, dominated convergence — with dominating function $x^2$, integrable for a Gaussian — gives $\int x^2\,dN(0,v) \le B$. Finally the second moment of $N(0,v)$ is its variance, since the mean vanishes, and that is $v$.
-- source:
--   P. Billingsley, Convergence of Probability Measures, 2nd ed., Wiley 1999, Section 3 (uniform integrability and moment convergence); P. Billingsley, Probability and Measure, 3rd ed., Wiley 1995, Theorem 25.11; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320.

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.gaussian_variance_le_of_tendstoInDistribution {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (v : ℝ≥0) (B : ℝ) (hY : ∀ n, Measurable (Y n))
    (hclt : TendstoInDistribution Y atTop (id : ℝ → ℝ) (fun _ => μ) (gaussianReal 0 v))
    (hint : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μ)
    (hbd : ∀ n, ∫ ω, (Y n ω) ^ 2 ∂μ ≤ B) :
    (v : ℝ) ≤ B := by sorry

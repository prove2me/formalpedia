-- Prove2me | Theorems.Thm_MarkovChainCLT_tendstoInDistribution_inv_sqrt_of_normalized
-- name    : MarkovChainCLT.tendstoInDistribution_inv_sqrt_of_normalized
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T07:32:54.472858+00:00
-- url     : https://prove2.me/theorems/7ed75cf3-0569-4c5c-8245-7e390827852f
-- title:
--   Change of normalization from $\sigma_n$ to $\sqrt n$ in a Gaussian limit
-- statement:
--   Let $(X_n)_{n\ge1}$ be real random variables on a probability space and $(d_n)$ positive normalizing constants such that the self-normalized sequence converges in distribution to a standard Gaussian,
--
--   $$\frac{X_n}{d_n}\ \xrightarrow{d}\ N(0,1),$$
--
--   and such that $d_n/\sqrt n\to s$ with $s>0$. Then the same sequence normalized by $\sqrt n$ converges to the Gaussian law of variance $s^2$:
--
--   $$\frac{X_n}{\sqrt n}\ \xrightarrow{d}\ N(0,s^2).$$
--
--   This is the change-of-normalization step in central limit theorems for dependent sequences: results such as the characterization of the CLT by uniform integrability are stated for $X_n/\sqrt{\mathrm{Var}(X_n)}$, whereas the conclusion sought is for $X_n/\sqrt n$. Since the ratio of the two normalizations is a deterministic sequence converging to $s$, the statement is an instance of Slutsky's theorem together with the scaling identity $s\cdot N(0,1)=N(0,s^2)$.
--
--   **Formalization Note** Convergence in distribution is weak convergence of the laws, the limit being the identity random variable on $\mathbb R$ under the Gaussian measure; the variance of the limit is written as the nonnegative-real coercion of $s^2$.
-- source:
--   Slutsky's theorem together with the scaling property of the Gaussian law; used in this form in G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorems 3 and 5-8, where the CLT is stated once with the normalization sqrt(Var S_n) and once with sqrt(n). See P. Billingsley, Convergence of Probability Measures, 2nd ed. (1999), Theorem 3.1.

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.tendstoInDistribution_inv_sqrt_of_normalized
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (d : ℕ → ℝ) (s : ℝ) (hs : 0 < s)
    (hX : ∀ n, Measurable (X n))
    (hd : Tendsto (fun n : ℕ => d n / Real.sqrt n) atTop (𝓝 s))
    (hnorm : TendstoInDistribution (fun (n : ℕ) ω => X n ω / d n) atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1)) :
    TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * X n ω) atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal (s ^ 2))) := by sorry

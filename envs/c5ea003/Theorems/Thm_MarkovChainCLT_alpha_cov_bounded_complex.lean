-- Prove2me | Theorems.Thm_MarkovChainCLT_alpha_cov_bounded_complex
-- name    : MarkovChainCLT.alpha_cov_bounded_complex
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T08:54:10.540939+00:00
-- url     : https://prove2.me/theorems/6a0e4b13-d463-435a-b05c-622a21eab6d7
-- title:
--   Covariance inequality under strong mixing, complex bounded variables: $|E[UV]-E[U]E[V]|\le 16AB\,\alpha(n)$
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space carrying a measurable process $Y=(Y_i)_{i\ge0}$, and let $\alpha(n)$ be its strong mixing coefficient at lag $n$,
--
--   $$\alpha(n)=\sup_k\sup\bigl\{|P(A\cap B)-P(A)P(B)|:A\in\sigma(Y_0,\dots,Y_k),\ B\in\sigma(Y_{k+n},Y_{k+n+1},\dots)\bigr\}.$$
--
--   Let $U$ be a bounded complex random variable measurable with respect to the past $\sigma(Y_0,\dots,Y_k)$, and $V$ a bounded complex random variable measurable with respect to the future $\sigma(Y_{k+n},\dots)$, with $\|U\|_\infty\le A$ and $\|V\|_\infty\le B$. Then
--
--   $$\bigl|E[UV]-E[U]\,E[V]\bigr|\;\le\;16\,A\,B\,\alpha(n).$$
--
--   This is the complex-valued form of the classical covariance inequality for bounded random variables under strong mixing. It is the estimate on which every characteristic-function proof of a central limit theorem for mixing sequences rests: applied to $U=\exp(it\,S')$ and $V=\exp(it\,S'')$ with $S'$ and $S''$ sums over blocks of indices separated by a gap of length $n$, it says that the characteristic function of a sum of well-separated blocks factorizes up to an error $16\alpha(n)$ per junction, which is what makes the Bernstein big-block/small-block scheme work.
--
--   The constant $16$ is $4$ times the constant $4$ of the real-valued inequality $|\operatorname{cov}(U,V)|\le 4\|U\|_\infty\|V\|_\infty\alpha(n)$: splitting $U$ and $V$ into real and imaginary parts produces four real covariances, and the real and imaginary parts of the complex covariance are each a sum of two of them.
--
--   **Formalization Note** Boundedness is stated pointwise rather than almost everywhere, and the two bounds $A$ and $B$ are separate, so that the inequality can be applied directly to normalized variables. Measurability with respect to the past and the future is stated with respect to the σ-algebras `processSigma Y (Set.Iic k)` and `processSigma Y (Set.Ici (k + n))` used to define the mixing coefficient itself.
-- source:
--   R. C. Bradley, "Basic Properties of Strong Mixing Conditions. A Survey and Some Open Questions", Probability Surveys 2 (2005) 107-144, Theorem 4.4 (covariance inequality for bounded random variables under the strong mixing condition); I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables (1971), Lemma 17.2.1 and its use in Theorem 18.5.3; the complex form is the standard version used for characteristic functions.

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.alpha_cov_bounded_complex {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ n, Measurable (Y n)) (n k : ℕ) (U V : Ω → ℂ)
    (hU : Measurable[processSigma Y (Set.Iic k)] U)
    (hV : Measurable[processSigma Y (Set.Ici (k + n))] V)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hUb : ∀ ω, ‖U ω‖ ≤ A) (hVb : ∀ ω, ‖V ω‖ ≤ B) :
    ‖(∫ ω, U ω * V ω ∂P) - (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P)‖
      ≤ 16 * A * B * alphaMixingCoef P Y n := by sorry

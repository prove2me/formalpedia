-- Prove2me | Theorems.Thm_MarkovChainCLT_abs_covariance_le_two_mul_sqrt_phiMixingCoef
-- name    : MarkovChainCLT.abs_covariance_le_two_mul_sqrt_phiMixingCoef
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-04T22:39:57.48956+00:00
-- url     : https://prove2.me/theorems/2c170d7a-b594-4c94-9529-71b88c52fdc3
-- title:
--   Ibragimov's covariance inequality: $|\\operatorname{cov}(U,V)| \\le 2\\sqrt{\\varphi(n)}\\,\\sigma_U \\sigma_V$
-- statement:
--   Let $(Y_i)_{i \ge 0}$ be a sequence of random variables on a probability space $(\Omega, \mathcal F, P)$, let $k, n \ge 0$, and let
--
--   $$\mathcal A = \sigma(Y_0, \dots, Y_k), \qquad \mathcal B = \sigma(Y_{k+n}, Y_{k+n+1}, \dots)$$
--
--   be the corresponding past and future $\sigma$-algebras. Let $\varphi(n)$ denote the uniform (φ-) mixing coefficient of the sequence at lag $n$,
--
--   $$\varphi(n) = \sup_{k}\ \sup\left\{ \left| P(B \mid A) - P(B) \right| : A \in \sigma(Y_0,\dots,Y_k),\ P(A) \neq 0,\ B \in \sigma(Y_{k+n}, \dots) \right\}.$$
--
--   Then for all square-integrable $U$ measurable with respect to $\mathcal A$ and $V$ measurable with respect to $\mathcal B$,
--
--   $$\bigl|\operatorname{cov}(U, V)\bigr| \;\le\; 2\sqrt{\varphi(n)}\,\sqrt{\operatorname{Var} U}\,\sqrt{\operatorname{Var} V}.$$
--
--   This is Ibragimov's covariance inequality in the case $p = q = 2$: it is the pairwise form of the Cogburn–Ibragimov comparison $\rho(n) \le 2\sqrt{\varphi(n)}$ between the maximal-correlation and uniform-mixing coefficients, and taking the supremum over all admissible pairs $(U,V)$ turns this inequality into that comparison.
--
--   The classical argument interpolates between two endpoint estimates for the centered conditional-expectation operator $S g = E[g \mid \mathcal A] - E g$ acting on $\mathcal B$-measurable variables, namely $\|S\|_{L^\infty \to L^\infty} \le 2\varphi(\mathcal A, \mathcal B)$ and $\|S\|_{L^1 \to L^1} \le 2\varphi(\mathcal B, \mathcal A) \le 2$; the geometric mean of the two bounds gives $\|S\|_{L^2 \to L^2} \le 2\sqrt{\varphi(\mathcal A, \mathcal B)}$, and Cauchy–Schwarz then yields the displayed covariance bound. An interpolation-free route to the same $L^2$ bound uses that $T = S^{*}S$ is positive and self-adjoint, so that $\langle T g, g\rangle^{2^m} \le \langle T^{2^m} g, g\rangle$ by iterated Cauchy–Schwarz, while $\|T^{2^m} g\|_2^2 \le \|T^{2^m} g\|_\infty \|T^{2^m} g\|_1$ controls the right-hand side by the endpoint norms; letting $m \to \infty$ gives $\|T\| \le 4\varphi$.
-- source:
--   R. C. Bradley, "Basic Properties of Strong Mixing Conditions. A Survey and Some Open Questions", Probability Surveys 2 (2005) 107-144, arXiv:math/0511078v1, Section 1.1, eq. (1.13): rho(A,B) <= 2[phi(A,B)]^{1/2}[phi(B,A)]^{1/2}, attributed there to Cogburn (1960) and Ibragimov (1962); this problem is the pairwise (covariance) form of that inequality, i.e. Ibragimov's covariance inequality with p = q = 2; see also J. L. Doob, Stochastic Processes (1953), p. 222, Lemma 7.1.

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory

theorem MarkovChainCLT.abs_covariance_le_two_mul_sqrt_phiMixingCoef
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n k : ℕ) (U V : Ω → ℝ)
    (hU : Measurable[processSigma Y (Set.Iic k)] U)
    (hV : Measurable[processSigma Y (Set.Ici (k + n))] V)
    (hU2 : MemLp U 2 P) (hV2 : MemLp V 2 P) :
    |cov[U, V; P]| ≤ 2 * Real.sqrt (phiMixingCoef P Y n) *
      (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P])) := by sorry

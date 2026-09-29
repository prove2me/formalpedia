-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_tv_rate
-- name    : MarkovChainCLT.clt_of_tv_rate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:40:10.716205+00:00
-- url     : https://prove2.me/theorems/430d0d6d-77f1-4974-abf5-d9f629ee543c
-- title:
--   Chain CLT from a TV rate: $E_\pi|f|^{2+\delta}<\infty$, $\sum \gamma(n)^{\delta/(2+\delta)}<\infty$ (Jones Cor 1)
-- statement:
--   Let $X = \{X_n\}_{n \ge 0}$ be a Markov chain with transition kernel $P$ on a state space $\mathsf{X}$, Harris ergodic with invariant probability distribution $\pi$, and let $f : \mathsf{X} \to \mathbb{R}$ be measurable. Write $\bar f_n = n^{-1} \sum_{i=1}^{n} f(X_i)$ for the sample average and $E_\pi f = \int f \, d\pi$. Suppose the total-variation rate bound $\|P^n(x, \cdot) - \pi\| \le M(x)\, \gamma(n)$ holds for all $x$ and all $n \ge 1$, with $M \ge 0$ integrable with respect to $\pi$ and $\gamma \ge 0$ nonincreasing, and that for some $\delta > 0$,
--
--   $$
--   E_\pi |f|^{2+\delta} < \infty \qquad \text{and} \qquad \sum_n \gamma(n)^{\delta/(2+\delta)} < \infty.
--   $$
--
--   Then the chain satisfies the central limit theorem for $f$: there is a single asymptotic variance $\sigma_f^2 \ge 0$ such that for every initial distribution of the chain,
--
--   $$
--   \sqrt{n}\,\bigl(\bar f_n - E_\pi f\bigr) \xrightarrow{d} N(0, \sigma_f^2) \qquad (n \to \infty).
--   $$
--
--   This is the source's master corollary (its eq. (11)): any total-variation rate plus a matching moment yields the CLT, uniformly over initial distributions; all remaining chain CLTs of the mission are specializations.
--
--   **Formalization Note** "Harris ergodic" is encoded by its total-variation characterization: $\pi$ is invariant for $P$ and $\|P^n(x, \cdot) - \pi\| \to 0$ for every starting point $x$ (equivalent to the classical aperiodic, $\psi$-irreducible, positive Harris recurrent definition; the "every $x$" quantifier is exactly the Harris property). Convergence in distribution is weak convergence of laws, and $N(0, 0)$ is read as the point mass at $0$, which absorbs the source's "$\sigma_f^2 > 0$" caveat.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Corollary 1, eq. (11) (arXiv v2 p. 10; proved there from Theorem 5 via Theorem 2(ii) and Meyn-Tweedie Proposition 17.1.6)

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Corollary 1**: a Harris ergodic chain with total-variation rate `γ`
(nonnegative, nonincreasing) and integrable constant `M`, and a functional with
`E_π |f|^{2+δ} < ∞` for a `δ > 0` such that `∑_n γ(n)^{δ/(2+δ)} < ∞`, satisfies the
CLT for every initial distribution. -/

theorem MarkovChainCLT.clt_of_tv_rate {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (M : X → ℝ) (hM0 : ∀ x, 0 ≤ M x) (hM : Integrable M π)
    (γ : ℕ → ℝ) (hγ0 : ∀ n, 0 ≤ γ n) (hγa : Antitone γ)
    (hrate : ErgodicWithRate P π M γ)
    (δ : ℝ) (hδ : 0 < δ) (hmom : Integrable (fun x => |f x| ^ (2 + δ)) π)
    (hsum : Summable (fun n => γ n ^ (δ / (2 + δ)))) :
    SatisfiesCLT P π f := by sorry

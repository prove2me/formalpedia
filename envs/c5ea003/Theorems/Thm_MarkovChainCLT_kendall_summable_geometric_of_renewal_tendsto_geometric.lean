-- Prove2me | Theorems.Thm_MarkovChainCLT_kendall_summable_geometric_of_renewal_tendsto_geometric
-- name    : MarkovChainCLT.kendall_summable_geometric_of_renewal_tendsto_geometric
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-07T02:42:03.430713+00:00
-- url     : https://prove2.me/theorems/0e044872-0bb6-46ba-a72b-ec2133863bb5
-- title:
--   Kendall's renewal theorem: geometric convergence of $v_n$ forces $\sum_k a_k\kappa^k<\infty$
-- statement:
--   **Kendall's renewal theorem, the geometric-convergence direction.** Let $a = (a_k)_{k \ge 1}$ be a probability distribution on the positive integers ($a_k \ge 0$, $a_0 = 0$, $\sum_k a_k = 1$), and let $v$ be its **renewal sequence**: $v_0 = 1$ and
--
--   $$v_n = \sum_{k=1}^{n} a_k\, v_{n-k} \qquad (n \ge 1),$$
--
--   so that $v_n$ is the probability that a renewal occurs at time $n$ when inter-renewal times are i.i.d. with law $a$. Suppose $v$ converges **geometrically** to a **positive** limit: there are $v_\infty > 0$, $M$ and $\rho \in [0,1)$ with
--
--   $$|v_n - v_\infty| \le M\,\rho^n \qquad (n \ge 0).$$
--
--   Then the inter-renewal law has a **geometric tail**: there is $\kappa > 1$ with
--
--   $$\sum_{k} a_k\, \kappa^k < \infty .$$
--
--   This is the implication (i) $\Rightarrow$ (ii) of Kendall's Theorem as stated in Meyn and Tweedie (Theorem 15.1.1), and it is the analytic engine behind the equivalence "geometric ergodicity $\Leftrightarrow$ geometric drift" (their Theorem 15.0.1) that the source invokes in Remark 1. In the present mission it is what the remaining open leaf `geoDriftCondition_of_geometricallyErgodic` needs: applied to the renewal sequence $v_k = \varepsilon\,(Q P^{n_0(k-1)})(C)$ of a small set $C$ with minorization $P^{n_0}(x,\cdot) \ge \varepsilon Q$ on $C$ (and $Q$ concentrated where the geometric rate constant is bounded), it turns the geometric total-variation convergence at the points of $C$ into geometric tails for the regeneration times, which is condition (ii) of Theorem 15.0.1 and yields the drift function $V(x) = E_x\bigl[\sum_{k \le \sigma_C} \kappa^k\bigr]$.
--
--   **Proof idea.** Write $A(z) = \sum_k a_k z^k$ and $V(z) = \sum_n v_n z^n$ for $|z| < 1$; the renewal equation is $V(z)(1 - A(z)) = 1$. The hypothesis says $H(z) = \sum_n (v_n - v_\infty) z^n$ is analytic on $|z| < 1/\rho$, so $G(z) := (1-z)V(z) = v_\infty + (1-z)H(z)$ extends analytically to $|z| < 1/\rho$ and satisfies $G(z)(1 - A(z)) = 1 - z$ on the open unit disc. $G$ has no zero on the closed unit disc: $G(1) = v_\infty > 0$, and at a point $z_0 \neq 1$ of the unit circle a zero of $G$ would force $|1 - A(r z_0)| = |1 - r z_0|/|G(r z_0)| \to \infty$ as $r \uparrow 1$, contradicting $|A| \le 1$. By compactness $G$ is zero-free on a disc $|z| < r$ with $r > 1$, so $1 - (1-z)/G(z)$ is analytic there and coincides with $A$ on the unit disc; uniqueness of power series coefficients and Cauchy's estimates give $\sum_k a_k \kappa^k < \infty$ for every $1 < \kappa < r$. No aperiodicity hypothesis is needed: it is implied by the convergence of $v_n$ to a positive limit.
--
--   **Formalization Note** The renewal recursion is written with the index shift $v_{n+1} = \sum_{j=0}^{n} a_{j+1} v_{n-j}$ to keep natural-number subtraction honest. The distribution is normalised by `HasSum a 1`; the limit $v_\infty$ must be positive (for a defective or periodic law the renewal sequence does not converge geometrically to a positive limit, so nothing is lost). The conclusion is stated as summability of $a_k \kappa^k$ for some $\kappa > 1$, the form in which it is consumed (a finite geometric moment of the inter-renewal time).
-- source:
--   S. P. Meyn & R. L. Tweedie, Markov Chains and Stochastic Stability, Springer 1993 (2nd ed. Cambridge University Press 2009), Theorem 15.1.1 (Kendall's Theorem), implication (i) => (ii); original: D. G. Kendall, "Unitary dilations of Markov transition operators, and the corresponding integral representations for transition-probability matrices", in U. Grenander (ed.), Probability and Statistics: The Harald Cramér Volume, Almqvist & Wiksell, Stockholm, 1959, pp. 139-161. Role in the mission: G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 2, Remark 1 (arXiv v2 pp. 3-4): "geometric ergodicity is equivalent to (5) (Meyn and Tweedie, 1993, Chapter 16)", whose proof (Theorem 15.0.1, (i) => (ii)) rests on Kendall's theorem.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Filter
open scoped Topology BigOperators

theorem MarkovChainCLT.kendall_summable_geometric_of_renewal_tendsto_geometric
    (a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (ha_zero : a 0 = 0) (hsum : HasSum a 1)
    (v : ℕ → ℝ) (hv0 : v 0 = 1)
    (hv : ∀ n : ℕ, v (n + 1) = ∑ j ∈ Finset.range (n + 1), a (j + 1) * v (n - j))
    (vlim M ρ : ℝ) (hvlim : 0 < vlim) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hconv : ∀ n : ℕ, |v n - vlim| ≤ M * ρ ^ n) :
    ∃ κ : ℝ, 1 < κ ∧ Summable (fun k : ℕ => a k * κ ^ k) := by sorry

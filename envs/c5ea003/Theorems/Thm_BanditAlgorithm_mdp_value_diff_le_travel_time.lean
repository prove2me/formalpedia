-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_value_diff_le_travel_time
-- name    : BanditAlgorithm.mdp_value_diff_le_travel_time
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T04:50:03.065017+00:00
-- url     : https://prove2.me/theorems/57dbfc2e-4192-4b8b-83da-c32d5af4713d
-- title:
--   Bias differences are bounded by the expected travel time
-- statement:
--   Let $(\rho, v)$ satisfy the Bellman optimality inequality
--
--   $$r_a(s) + \langle P_a(s), v\rangle \;\le\; \rho + v(s) \qquad \text{for all } s, a,$$
--
--   with $v$ bounded, and let $f$ be a memoryless deterministic policy whose expected travel time from $\mathrm{src}$ to $\mathrm{tgt}$ is finite. Then
--
--   $$v(\mathrm{tgt}) - v(\mathrm{src}) \;\le\; \rho \cdot \mathbb{E}^{f}\big[\tau_{\mathrm{tgt}} - 1 \mid S_1 = \mathrm{src}\big],$$
--
--   the expectation on the right being exactly the travel time of Lattimore and Szepesvári, Definition 38.1 (their diameter is the maximin of this quantity over pairs of states and policies).
--
--   This is the displayed inequality of L&S Exercise 38.13, and taking the minimum over $f$ and the maximum over pairs of states turns it into Lemma 38.3, $\mathrm{span}(v) \le \rho^{*} D(M)$, the estimate that bounds the boundary term of every phase of UCRL2 by the diameter. Note that only the reward bound $r \ge 0$ of the MDP structure is used, so the factor is $\rho$ rather than $\rho - \min_{s,a} r_a(s)$.
--
--   The proof accumulates the Bellman inequality along the trajectory, stopped at the hitting time $\tau$ of $\mathrm{tgt}$. Writing $\chi_k$ for the indicator that none of the first $k$ states is $\mathrm{tgt}$, the quantity
--
--   $$\Phi_n \;=\; \mathbb{E}\Big[\chi_n\big(\langle P_{A_n}(S_n), v\rangle - v(\mathrm{tgt})\big) + \sum_{t \le n} \chi_t\,\big(r_{A_t}(S_t) - \rho\big)\Big]$$
--
--   is non-increasing: the summand contributed by a round is unchanged once the target has been reached, and before that the Bellman inequality applies. Hence $\Phi_n \le \Phi_0 = v(\mathrm{src}) - v(\mathrm{tgt})$ for every $n$. Bounding the two pieces of $\Phi_n$ from below by $-\mathrm{span}(v)\,\mathbb{P}(\tau > n)$ and $-\rho \sum_{t \le n} \mathbb{P}(\tau > t)$ and letting $n \to \infty$ gives the claim, the first term vanishing because the series $\sum_t \mathbb{P}(\tau > t)$ converges.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Exercise 38.13 (the hint's displayed inequality) and Lemma 38.3, Section 38.2; Puterman, Markov Decision Processes (Wiley 1994), Chapter 8; Jaksch, Ortner & Auer, Near-optimal Regret Bounds for Reinforcement Learning, JMLR 11 (2010), Section 4.3.1.

import Definitions.Def_FiniteMDPLearning
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_value_diff_le_travel_time {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (src tgt : Fin S) (ρ : ℝ) (v : Fin S → ℝ) (lo hi : ℝ)
    (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s)
    (hfin : mdpTravelTime M f src tgt ≠ ⊤) :
    v tgt - v src ≤ ρ * (mdpTravelTime M f src tgt).toReal := by
  sorry

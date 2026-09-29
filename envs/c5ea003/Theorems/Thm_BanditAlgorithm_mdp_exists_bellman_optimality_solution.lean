-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_exists_bellman_optimality_solution
-- name    : BanditAlgorithm.mdp_exists_bellman_optimality_solution
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T15:14:28.973092+00:00
-- url     : https://prove2.me/theorems/01dcb9e5-d29a-439b-9fcd-9ca61d037f50
-- title:
--   Existence of a Bellman optimality solution for a finite MDP
-- statement:
--   Let $M$ be a finite MDP with $S \ge 1$ states, $A \ge 1$ actions, rewards $r_a(s) \in [0,1]$ and finite diameter $D(M) < \infty$. Then there exist a gain $\rho \in [0,1]$, a value function $v : \mathcal{S} \to \mathbb{R}$, and a deterministic memoryless policy $f : \mathcal{S} \to \mathcal{A}$ such that
--
--   $$\mathrm{span}(v) \;\le\; \rho\, D(M), \qquad r_a(s) + \langle P_a(s), v\rangle \;\le\; \rho + v(s) \ \ \text{for all } a, \qquad \rho + v(s) \;=\; r_{f(s)}(s) + \langle P_{f(s)}(s), v\rangle,$$
--
--   and $\rho = \rho^{*}$ is the optimal gain of $M$. The last two displays together say that $(\rho, v)$ solves the average-reward Bellman optimality equation
--
--   $$\rho + v(s) \;=\; \max_{a} \big( r_a(s) + \langle P_a(s), v\rangle \big),$$
--
--   with $f$ a greedy — hence gain-optimal — policy; since $\rho \le 1$ the span bound gives $\mathrm{span}(v) \le D(M)$.
--
--   This is Theorem 38.2 of Lattimore and Szepesvári, whose proof is left to their Exercise 38.10. It is what makes UCRL2 well defined: the algorithm computes an optimistic solution of the optimality equation of the extended MDP and plays greedily, and both the optimism step (Eq. 38.17) and the span bound of Eq. (38.19) are read off the equation.
--
--   The proof is the vanishing-discount argument. For each $\gamma < 1$ let $V_\gamma$ be the $\gamma$-discounted value function and put $\rho_\gamma = (1-\gamma)\max_s V_\gamma(s) \in [0,1]$. Splitting $\langle P_a(s), V_\gamma\rangle$ as $\gamma\langle P_a(s), V_\gamma\rangle + (1-\gamma)\langle P_a(s), V_\gamma\rangle$ and bounding the second term by $(1-\gamma)\max_s V_\gamma(s)$ shows that $(\rho_\gamma, V_\gamma)$ solves the average-reward Bellman *inequality*; hence $\mathrm{span}(V_\gamma) \le \rho_\gamma D(M) \le D(M)$, uniformly in $\gamma$. The recentred functions $V_\gamma - V_\gamma(s_0)$ therefore range in the compact cube $[-D, D]^{\mathcal S}$ while $\rho_\gamma$ ranges in $[0,1]$, and the greedy policies range over a finite set; so along a subsequence $\gamma_k \uparrow 1$ the greedy policy is a fixed $f$ and the pair converges. In the limit the inequality persists, and the defect in the greedy equality — which equals $(1-\gamma)\big(\max_s V_\gamma(s) - \langle P_{f(s)}(s), V_\gamma\rangle\big)$ and so lies between $0$ and $(1-\gamma) D(M)$ — vanishes. That $\rho$ is the optimal gain is then the two halves of the verification argument: the inequality gives $\rho^{*} \le \rho$ and the equality along $f$ gives $\rho \le \rho^{*}$.
--
--   The uniform span bound is exactly the point at which the finiteness of the diameter enters; without it the recentred discounted value functions need not be bounded and the limit may fail to exist.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Theorem 38.2 (Section 38.2, printed p. 521 / PDF p. 530; proof left to Exercise 38.10); Puterman, Markov Decision Processes (Wiley 1994), Chapter 8 (the vanishing-discount approach to the average-reward optimality equation).

import Definitions.Def_FiniteMDPLearning
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_exists_bellman_optimality_solution {S A : ℕ} (hS : 0 < S)
    (hA : 0 < A) (M : FiniteMDP S A) (hD : mdpDiameterENN M ≠ ⊤) :
    ∃ (ρ : ℝ) (v : Fin S → ℝ) (f : Fin S → Fin A),
      0 ≤ ρ ∧ ρ ≤ 1 ∧
      (∀ s s', v s - v s' ≤ ρ * mdpDiameter M) ∧
      (∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s) ∧
      (∀ s, ρ + v s = M.r s (f s) + ∑ s', (M.P s (f s) s' : ℝ) * v s') ∧
      mdpOptimalGain M = ρ := by
  sorry

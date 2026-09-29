-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_expected_reward_le_of_bellman_ineq
-- name    : BanditAlgorithm.mdp_expected_reward_le_of_bellman_ineq
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T04:33:08.982034+00:00
-- url     : https://prove2.me/theorems/fc83c0c7-aca4-4a69-9545-3d504793ef03
-- title:
--   Bellman optimality inequality upper-bounds the expected reward
-- statement:
--   Let $M$ be a finite MDP and suppose the pair $(\rho, v)$ satisfies the Bellman optimality *inequality*
--
--   $$r_a(s) + \langle P_a(s), v\rangle \;\le\; \rho + v(s) \qquad \text{for all states } s \text{ and actions } a,$$
--
--   with $v$ taking values in $[\mathrm{lo}, \mathrm{hi}]$. Then for every policy $\pi$, every initial distribution $\mu_0$ and every horizon $n$,
--
--   $$\mathbb{E}\Big[\sum_{t=1}^{n} r_{A_t}(S_t)\Big] \;\le\; n\rho + \big(\mathrm{hi} - \mathrm{lo}\big).$$
--
--   The error term is the span of $v$, and the bound holds for arbitrary history-dependent randomised policies, with no communication or ergodicity assumption on $M$.
--
--   This is the finite-horizon estimate underlying Theorem 38.2 of Lattimore and Szepesvári, and it is what the analysis of UCRL2 consumes: in phase $k$ the algorithm solves the Bellman optimality equation of the extended MDP, and because the true MDP lies in the confidence set its own rows satisfy the inequality above, which yields the optimism $\rho^* \le \rho_k$ of Eq. (38.17).
--
--   The proof accumulates the inequality along the interaction. Writing $V_t = v(S_t)$, the hypothesis gives $r_{A_t}(S_t) \le \rho + v(S_t) - \langle P_{A_t}(S_t), v\rangle$, and the last term is the conditional expectation of $v(S_{t+1})$ given the history, so the quantity $\sum_{t \le T} r_{A_t}(S_t) + v(S_{T+1}) - T\rho$ is non-increasing in expectation. Formally one shows by induction on the horizon, using the Markov property of the trajectory measure, that the expected reward of $n$ rounds plus the expected value of the state reached after them is at most $n\rho + \langle \mu_0, v\rangle$; discarding the terminal value costs at most $\mathrm{hi} - \mathrm{lo}$.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Section 38.2, Theorem 38.2 and Eq. (38.17) in Step 1 of the proof of Theorem 38.6; Puterman, Markov Decision Processes (Wiley 1994), Chapter 8; Jaksch, Ortner & Auer, Near-optimal Regret Bounds for Reinforcement Learning, JMLR 11 (2010), Section 4.3.

import Definitions.Def_FiniteMDPLearning
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_expected_reward_le_of_bellman_ineq {S A : ℕ}
    (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (π : MDPPolicy S A)
    (ρ : ℝ) (v : Fin S → ℝ) (lo hi : ℝ) (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s) (n : ℕ) :
    mdpExpectedReward M μ0 π n ≤ n * ρ + (hi - lo) := by
  sorry

-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_expected_reward_ge_of_reverse_bellman_ineq
-- name    : BanditAlgorithm.mdp_expected_reward_ge_of_reverse_bellman_ineq
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T15:10:54.427383+00:00
-- url     : https://prove2.me/theorems/44ee2a44-b5d2-4f26-b26b-ab41ae826c0b
-- title:
--   Reverse Bellman inequality lower-bounds the expected reward
-- statement:
--   Let $M$ be a finite MDP, $f : \mathcal{S} \to \mathcal{A}$ a deterministic memoryless policy, $\rho \in \mathbb{R}$, and $v : \mathcal{S} \to \mathbb{R}$ taking values in $[\mathrm{lo}, \mathrm{hi}]$, and suppose the *reverse* Bellman inequality holds along $f$:
--
--   $$\rho + v(s) \;\le\; r_{f(s)}(s) + \langle P_{f(s)}(s), v\rangle \qquad \text{for every state } s .$$
--
--   Then for every initial distribution $\mu$ and every horizon $n$,
--
--   $$\mathbb{E}^{f}\Big[\sum_{t=1}^{n} r_{A_t}(S_t)\Big] \;\ge\; n\rho - \big(\mathrm{hi} - \mathrm{lo}\big).$$
--
--   This is the mirror image of the estimate behind the verification half of Theorem 38.2 of Lattimore and Szepesvári, and supplies its optimality half: a pair $(\rho, v)$ solving the average-reward Bellman optimality *equation* satisfies both inequalities, so the greedy policy $f$ collects at least $n\rho$ up to the span of $v$, whence its gain is exactly $\rho$ and $\rho = \rho^{*}$.
--
--   The proof is the same telescoping run backwards. Writing $\Phi_n = \mathbb{E}^{f}\big[\sum_{t \le n} r_{A_t}(S_t) + v(S_{n+1})\big]$, one step of the interaction protocol together with the reverse inequality gives $\Phi_{n+1} \ge \Phi_n + \rho$, and $\Phi_0 = \langle \mu, v\rangle$, so $\Phi_n \ge n\rho + \langle \mu, v\rangle$. Discarding the terminal value $\mathbb{E}[v(S_{n+1})] \le \mathrm{hi}$ and bounding $\langle \mu, v\rangle \ge \mathrm{lo}$ costs exactly the span of $v$. Every integrability side condition is automatic because the trajectory space of a fixed horizon is finite. The step where the action is determined by the current state uses that the policy's selection kernel is a Dirac mass at $f(s)$.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Section 38.2, the optimality half of Theorem 38.2 (proof left to Exercise 38.10); Puterman, Markov Decision Processes (Wiley 1994), Chapter 8 (average reward, the optimality equation and its greedy policy).

import Definitions.Def_FiniteMDPLearning
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_expected_reward_ge_of_reverse_bellman_ineq {S A : ℕ}
    (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (f : Fin S → Fin A) (ρ : ℝ)
    (v : Fin S → ℝ) (lo hi : ℝ) (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s, ρ + v s ≤ M.r s (f s) + ∑ s', (M.P s (f s) s' : ℝ) * v s') (n : ℕ) :
    (n : ℝ) * ρ - (hi - lo)
      ≤ mdpExpectedReward M μ0 (mdpMemorylessDetPolicy f) n := by
  sorry

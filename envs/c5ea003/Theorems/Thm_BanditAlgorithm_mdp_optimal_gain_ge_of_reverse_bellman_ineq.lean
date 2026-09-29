-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_optimal_gain_ge_of_reverse_bellman_ineq
-- name    : BanditAlgorithm.mdp_optimal_gain_ge_of_reverse_bellman_ineq
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T15:11:57.405339+00:00
-- url     : https://prove2.me/theorems/34d26fe8-9223-41bf-b457-a369f11c3ee6
-- title:
--   Reverse Bellman inequality lower-bounds the optimal gain
-- statement:
--   Let $M$ be a finite MDP with at least one state, $f : \mathcal{S} \to \mathcal{A}$ a deterministic memoryless policy, and $(\rho, v)$ with $v$ bounded satisfying the reverse Bellman inequality along $f$,
--
--   $$\rho + v(s) \;\le\; r_{f(s)}(s) + \langle P_{f(s)}(s), v\rangle \qquad \text{for every state } s .$$
--
--   Then $\rho \le \rho^{*}$, where $\rho^{*} = \max_{s} \sup_{\pi} \bar\rho^{\,s}_{\pi}$ is the optimal gain of $M$.
--
--   This is the optimality half of Theorem 38.2 of Lattimore and Szepesvári, complementing the verification half (a solution of the Bellman optimality *inequality* $r_a(s) + \langle P_a(s), v\rangle \le \rho + v(s)$ bounds $\rho^{*}$ from above). A pair $(\rho, v)$ solving the optimality *equation* satisfies both, so $\rho = \rho^{*}$ and the greedy policy $f$ is optimal.
--
--   The proof is the finite-horizon bound $\mathbb{E}^{f}[\sum_{t \le n} r_{A_t}(S_t)] \ge n\rho - \mathrm{span}(v)$ divided by $n$: the lower bounds $\rho - \mathrm{span}(v)/n$ converge to $\rho$, so the $\limsup$ defining the gain of $f$ from any state is at least $\rho$. The passage from the gain of one policy to the optimal gain is the elementary bound of a supremum by one of its terms; the supremum is finite because every gain is at most one, the rewards being in $[0,1]$, so the conditional supremum is well behaved.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Theorem 38.2 (Section 38.2, proof left to Exercise 38.10), the optimality half; Puterman, Markov Decision Processes (Wiley 1994), Chapter 8.

import Definitions.Def_FiniteMDPLearning
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_optimal_gain_ge_of_reverse_bellman_ineq {S A : ℕ} (hS : 0 < S)
    (M : FiniteMDP S A) (f : Fin S → Fin A) (ρ : ℝ) (v : Fin S → ℝ) (lo hi : ℝ)
    (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s, ρ + v s ≤ M.r s (f s) + ∑ s', (M.P s (f s) s' : ℝ) * v s') :
    ρ ≤ mdpOptimalGain M := by
  sorry

-- Prove2me | Theorems.Thm_BertsekasDP_dp_algorithm_optimality
-- name    : BertsekasDP.dp_algorithm_optimality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-04T16:51:25.02239+00:00
-- url     : https://prove2.me/theorems/24924747-2836-4a6d-8ec4-6c9e1c3d3112
-- title:
--   Optimality of the DP algorithm (Prop. 1.3.1)
-- statement:
--   **Proposition 1.3.1 (optimality of the dynamic programming algorithm).** Consider the basic problem with horizon $N$, system $x_{k+1} = f_k(x_k,u_k,w_k)$, finite nonempty constraint sets $U_k(x)$, finitely supported disturbances, and additive cost. Let $J_0$ be produced by the backward DP recursion $J_N = g_N$,
--
--   $$J_k(x) \;=\; \min_{u \in U_k(x)} \; \mathbb{E}_{w}\Bigl[g_k(x,u,w) + J_{k+1}\bigl(f_k(x,u,w)\bigr)\Bigr],$$
--
--   and call a policy $\pi = \{\mu_0,\dots,\mu_{N-1}\}$ admissible when $\mu_k(x) \in U_k(x)$ for every stage and state. Then for every initial state $x_0$,
--
--   $$J_0(x_0) \;=\; \min_{\pi \text{ admissible}} J_\pi(x_0),$$
--
--   and the minimum is attained: some admissible policy achieves exactly $J_0(x_0)$, and no admissible policy does better.
--
--   This is the theorem that licenses solving a multi-stage optimization one stage at a time. Every later result in this series is stated over the same model: the lookahead and rollout bounds of Chapter 6 compare a suboptimal policy's cost against this recursion, and the infinite-horizon theory of Chapter 7 studies the limit of iterating it.
--
--   **Formalization Note** The conclusion is phrased as a least element (`IsLeast`) of the set of achievable costs, which packages both halves — attainment and the lower bound — in one statement. Admissibility is required at every stage index, though only stages $0, \dots, N-1$ enter the cost. Policies are deterministic feedback maps of the current stage and state; this is the class over which the source states the result.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 1.3.1

import Mathlib
import Definitions.Def_BertsekasDPModel

namespace BertsekasDP

theorem dp_algorithm_optimality {S C W : Type} [Fintype W]
    (M : BertsekasDPModel S C W) (x₀ : S) :
    IsLeast {c : ℝ | ∃ π : ℕ → S → C, (∀ k x, π k x ∈ M.U k x) ∧
        c = BertsekasDPPolicyCost M π M.N x₀}
      (BertsekasDPValue M M.N x₀) := by sorry

end BertsekasDP

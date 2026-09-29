-- Prove2me | Theorems.Thm_BertsekasDP_minimax_dp_algorithm
-- name    : BertsekasDP.minimax_dp_algorithm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-04T16:52:27.541874+00:00
-- url     : https://prove2.me/theorems/40e6f1f3-b8cc-4b98-bedb-bb8cee654d54
-- title:
--   Validity of the minimax DP algorithm (§1.6)
-- statement:
--   **Validity of the minimax dynamic programming algorithm** (Bertsekas, Vol. I, §1.6, Eqs. (1.21)–(1.24)). Consider the minimax control problem with horizon $N$, system $x_{k+1} = f_k(x_k,u_k,w_k)$, finite nonempty constraint sets $U_k(x)$ and finite nonempty disturbance membership sets $W_k(x,u)$. Let $J_0$ be produced by the backward recursion $J_N = g_N$,
--
--   $$J_k(x) \;=\; \min_{u \in U_k(x)} \max_{w \in W_k(x,u)} \Bigl[g_k(x,u,w) + J_{k+1}\bigl(f_k(x,u,w)\bigr)\Bigr].$$
--
--   Then for every initial state $x_0$,
--
--   $$J_0(x_0) \;=\; \min_{\pi \text{ admissible}} \; \max_{w_0, \dots, w_{N-1}} \; \Bigl[g_N(x_N) + \sum_{k=0}^{N-1} g_k(x_k, \mu_k(x_k), w_k)\Bigr],$$
--
--   the worst case being taken over disturbances admissible at the controls actually played, and the minimum being attained by an admissible policy.
--
--   This is the minimax analogue of Prop. 1.3.1, and it shows that the dynamic programming principle survives the replacement of expectation by worst case — what the argument really needs is monotonicity of the stage operator, not averaging.
--
--   **Formalization Note** As for the stochastic version, the conclusion is a least element (`IsLeast`) of the set of achievable worst-case costs. The adversary in the policy-cost recursion re-chooses its disturbance at every stage as a function of the current state, so it is a closed-loop adversary; the interchange that makes this equivalent to the recursion above is Lemma 1.6.1.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 1.6, Eqs. (1.21)-(1.24)

import Mathlib
import Definitions.Def_BertsekasMinimaxDPModel

namespace BertsekasDP

theorem minimax_dp_algorithm {S C W : Type}
    (M : BertsekasMinimaxDPModel S C W) (x₀ : S) :
    IsLeast {c : ℝ | ∃ π : ℕ → S → C, (∀ k x, π k x ∈ M.U k x) ∧
        c = BertsekasMinimaxPolicyCost M π M.N x₀}
      (BertsekasMinimaxValue M M.N x₀) := by sorry

end BertsekasDP

-- Prove2me | Theorems.Thm_KServer_wfa_cost_le_growth
-- name    : KServer.wfa_cost_le_growth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T19:04:41.662316+00:00
-- url     : https://prove2.me/theorems/a3fd2869-f9b6-429f-a879-5f5f3028eed6
-- title:
--   The pseudocost bounds the Work Function Algorithm's cost plus the optimum
-- statement:
--   Let $u_0, u_1, \dots$ be step budgets bounding the growth of the work function: for each $t$ and **every** configuration $X$,
--
--   $$w_{\sigma|_{t+1}}(X) \;\le\; w_{\sigma|_t}(X) + u_t .$$
--
--   Then the Work Function Algorithm's own cost, together with the optimal offline cost, is bounded by their sum:
--
--   $$\mathrm{cost}_{\mathrm{WFA}}(\sigma) + \mathrm{opt}(\sigma) \;\le\; \sum_{t < |\sigma|} u_t .$$
--
--   ## Role
--
--   This is the *pseudocost method*: the quantity $r_s(w) = \max_X\{w^s(X) - w(X)\}$, the largest amount by which a request can raise the work function, is algorithm-independent and therefore easier to analyse than the algorithm's actual cost, and the pseudocost of a whole sequence dominates the cost of the Work Function Algorithm plus the optimum. To prove WFA $C$-competitive it therefore suffices to exhibit budgets summing to $(C+1)\,\mathrm{opt}(\sigma) + O(1)$ — a purely offline condition.
--
--   Stated as it is with budgets rather than with the maximum, the lemma composes directly with the potential-function criterion: a potential satisfying the offset and update properties supplies exactly such budgets, namely $u_t = \Phi_{\sigma|_t} - \Phi_{\sigma|_{t+1}}$.
--
--   The proof rests on a single identity relating the algorithm to the update operator. Writing $S_t$ for the algorithm's configuration after $t$ requests,
--
--   $$w_t(S_{t-1}) \;=\; w_t(S_t) + S_{t-1}S_t ,$$
--
--   which holds because the update operator computes $w_t(X)$ as the least value of $w_t(C) + CX$ over configurations $C$ containing the request, and the Work Function Algorithm moves to a configuration realising precisely that minimum. Rearranged, it says the algorithm's move at step $t$ costs exactly the drop in the work function at its previous configuration, so the algorithm's total cost telescopes; what is left over is $w_0(S_0) = 0$ at one end and $w_n(S_n) \ge \mathrm{opt}(\sigma)$ at the other.
--
--   **Formalization note.** The identity's two directions come from opposite sources: "$\le$" is the Lipschitz property of the work function, "$\ge$" is the minimality built into the algorithm's step, applied to the configuration produced by the one-step recursion for the work function. Because the algorithm is defined by an arbitrary choice among minimisers, only its minimality is used, never the choice itself.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Lemma 2 (attributed there to [1, 5, 9]): 'r_sigma >= cost_WFA(sigma) + opt(sigma)', where r_sigma is the pseudocost of the request sequence.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_work_function

namespace KServer

theorem wfa_cost_le_growth (k : ℕ) (hk : 0 < k) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (σ : List M) (u : ℕ → ℝ)
    (hu : ∀ t : ℕ, t < σ.length → ∀ X : Config k M,
      workFunction C₀ (σ.take (t + 1)) X ≤ workFunction C₀ (σ.take t) X + u t) :
    (WFA hk C₀).cost σ + offlineCost C₀ σ ≤ ∑ t ∈ Finset.range σ.length, u t := by sorry

end KServer

-- Prove2me | Theorems.Thm_KServer_online_cost_unlabelled_decomposition
-- name    : KServer.online_cost_unlabelled_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T22:14:02.783646+00:00
-- url     : https://prove2.me/theorems/cd08773a-51e2-4f15-9f8e-6f7f1ea1d5ba
-- title:
--   An online algorithm's cost splits into its laziness defect and its trajectory work-function growth
-- statement:
--   Let $A$ be any deterministic online $k$-server algorithm, let $A_t$ be its configuration after the first $t$ requests of $\sigma$, and let $w_t$ denote the classical (unlabelled) work function of the prefix $r_1 \dots r_t$. Write
--
--   $$\mathrm{move}_t = d(A_t, A_{t+1}), \qquad \mathrm{drop}_t = w_{t+1}(A_t) - w_{t+1}(A_{t+1}), \qquad g_t = w_{t+1}(A_t) - w_t(A_t).$$
--
--   Then
--
--   $$\mathrm{cost}(A, \sigma) \;+\; w_n(A_n) \;=\; \sum_{t<n}\bigl(\mathrm{move}_t - \mathrm{drop}_t\bigr) \;+\; \sum_{t<n} g_t.$$
--
--   The first sum is the algorithm's **laziness defect**: $\mathrm{drop}_t \le \mathrm{move}_t$ always, by $1$-Lipschitzness of the work function, and the summand vanishes exactly when the move the algorithm makes on the request $r_{t+1}$ buys a full matching decrease of the new work function --- when the algorithm is *lazy with respect to $w_{t+1}$*. The second sum is the total increase of the work function measured along the algorithm's own trajectory.
--
--   ## Role
--
--   This is an identity, valid for every online algorithm and every request sequence; no optimality, laziness or work-function-based behaviour is assumed of $A$. It isolates the two quantities that a competitive analysis has to control and separates them cleanly.
--
--   The second sum is bounded by the total *extended cost* $\sum_t \max_X (w_{t+1}(X) - w_t(X))$, which is the quantity the potential method exists to bound: Coester and Koutsoupias' potential yields $\sum_t \max_X (w_{t+1}(X) - w_t(X)) \le (k+1)\,\mathrm{OPT} + c_M$ on trees, and Chrobak--Larmore's and Koutsoupias' arguments yield $2k\,\mathrm{OPT} + c_M$ in general. Combined with $w_n(A_n) \ge \mathrm{OPT}$, the identity turns any bound of the form "laziness defect $\le b$" into competitiveness with ratio one less than the extended-cost constant: on trees, a bounded laziness defect gives $\mathrm{cost}(A,\sigma) \le k\,\mathrm{OPT} + (b + c_M)$.
--
--   The identity is therefore a reduction: for an algorithm whose definition is stated in terms of the work function, competitiveness is exactly a statement about how far its own moves fall short of being lazy for the unlabelled work function. This is the interesting case when the algorithm is defined through a *labelled* work function --- where a server's identity, not merely its position, is tracked --- since such an algorithm's moves need not be lazy for the unlabelled one, and the discrepancy is precisely the first sum.
--
--   ## Formalization note
--
--   $w$ is `workFnU`, obtained from the labelled work function by minimising over the relabellings of the target configuration; $\mathrm{cost}$ is the sum of the movement costs between successive configurations of $A$, and the initial configuration is $A(\varnothing)$. The proof is telescoping: the two summands combine to $\mathrm{move}_t + \bigl(w_{t+1}(A_{t+1}) - w_t(A_t)\bigr)$, and the second part telescopes to $w_n(A_n) - w_0(A_0)$ with $w_0(A_0) = 0$.
-- source:
--   The telescoping identity underlying the potential analyses of the Work Function Algorithm; see E. Koutsoupias, 'The k-server problem', Computer Science Review 3 (2009), Section 3, and C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021. Stated here for an arbitrary online algorithm, with the laziness defect isolated as a separate term.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem online_cost_unlabelled_decomposition (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (A : OnlineAlgorithm k M) (σ : List M) :
    A.cost σ + workFnU (A.conf []) σ (A.conf σ)
      = (∑ t ∈ Finset.range σ.length,
          (moveCost (A.conf (σ.take t)) (A.conf (σ.take (t + 1)))
            - (workFnU (A.conf []) (σ.take (t + 1)) (A.conf (σ.take t))
               - workFnU (A.conf []) (σ.take (t + 1)) (A.conf (σ.take (t + 1))))))
        + ∑ t ∈ Finset.range σ.length,
          (workFnU (A.conf []) (σ.take (t + 1)) (A.conf (σ.take t))
            - workFnU (A.conf []) (σ.take t) (A.conf (σ.take t))) := by sorry

end KServer

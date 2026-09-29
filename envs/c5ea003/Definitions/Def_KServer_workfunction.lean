-- Prove2me | Definitions.Def_KServer_workfunction
-- name    : KServer_workfunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-31T05:08:39.16402+00:00
-- url     : https://prove2.me/theorems/4190e22b-17b4-4a80-bf68-0fe2403c430b
-- title:
--   The work function: optimal offline cost of serving a request sequence and ending at a given configuration
-- statement:
--   Fix a metric space $M$, a number $k$ of servers, an initial configuration $C_0$ and a request sequence $\sigma=(r_1,\dots,r_t)$. The **work function** of Koutsoupias and Papadimitriou assigns to every configuration $X$ the cost of the best offline solution that starts at $C_0$, serves $\sigma$ in order, and finishes at $X$:
--
--   $$w(C_0;r_1,\dots,r_t;X)\;=\;\min\Bigl\{\textstyle\sum_{j=1}^{t+1} \mathrm{moveCost}(C_{j-1},C_j)\ :\ r_j\in C_j\ (1\le j\le t),\ C_{t+1}=X\Bigr\}.$$
--
--   Here the first $t$ moves serve the requests and the last one repositions the servers onto $X$. Taking the infimum over $X$ recovers the ordinary optimal offline cost, so the work function is a refinement of it that records *where* the optimum ends up, not just what it spends.
--
--   **Role.** The work function is the object every known general upper bound for the $k$-server problem is built on. The Work Function Algorithm serves a request $r_t$ by moving from its current configuration $C_{t-1}$ to a configuration $C_t$ containing $r_t$ that minimises $w_t(C_t)+d(C_{t-1},C_t)$, balancing the Greedy Algorithm, which ignores $w_t$ and has unbounded ratio, against the Retrospective Algorithm, which chases the minimiser of $w_t$ and is also unbounded. The Koutsoupias--Papadimitriou theorem that this algorithm is $(2k-1)$-competitive on every metric space, the $k$-competitiveness on spaces of $k+1$ and $k+2$ points, and the two-server case all run through its properties: the recurrence in $t$, the Lipschitz bound $w_t(X)\le w_t(Y)+d(X,Y)$, monotonicity in $t$, and quasiconvexity.
--
--   **Formalization Note** Configurations are the shared model's `Config k M = Fin k → M`, so the value is sensitive to which server ends where; the final move `moveCost (S σ.length) X` is what pins the endpoint. The definition is an `sInf` over the set of schedule costs, which is nonempty whenever $k\ge1$ and bounded below by $0$, so it behaves as a genuine minimum in the arguments that use it.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, equation (4) (definition of the work function) and Definition 1 (the Work Function Algorithm); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

/-- The **work function** of Koutsoupias--Papadimitriou: `workFn C₀ σ X` is the least cost
of an offline solution that starts at the configuration `C₀`, serves the request sequence
`σ` in order, and finishes in the configuration `X`.

Concretely it is the infimum, over all schedules `S` serving `σ` from `C₀`, of the total
movement along `S` plus the cost of one final move from `S`'s last configuration to `X`.
Taking the infimum over `X` recovers the ordinary optimal offline cost. -/
noncomputable def workFn {k : ℕ} {M : Type*} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : ℝ :=
  sInf {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X}

end KServer



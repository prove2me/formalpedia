-- Prove2me | Theorems.Thm_KServer_schedule_exists
-- name    : KServer.schedule_exists
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T03:47:16.397647+00:00
-- url     : https://prove2.me/theorems/02f7b6cb-a83f-4538-a584-6cd8e4e94cfa
-- title:
--   Offline schedules exist, so the optimum is an infimum of a nonempty set
-- statement:
--   Fix a metric space $M$, a number $k\ge1$ of servers, an initial configuration $C_0$, and a request sequence $\sigma=(r_1,\dots,r_n)$. An **offline schedule** for $\sigma$ from $C_0$ is a sequence of configurations $S_0=C_0, S_1, \dots$ in which $S_j$ places some server on $r_j$ for each $j\le n$; positions past $n$ are irrelevant.
--
--   **Statement.** At least one such schedule exists:
--   $$\exists\, S,\qquad S_0=C_0\ \text{ and }\ \forall j\le n,\ \exists i,\ S_j(i)=r_j .$$
--
--   **Role.** The optimal offline cost $\mathrm{OPT}(C_0,\sigma)$ is defined as an *infimum* over offline schedules, and an infimum over the empty set carries no information: in the reals it is $0$ by convention, so every bound proved about it would be vacuous. This lemma is what rules that out, and it is the hypothesis that both standard manipulations of $\mathrm{OPT}$ need — bounding it from below by exhibiting a lower bound for every schedule, and bounding it from above by exhibiting one schedule. The witness is the crudest possible schedule, which parks every server on each request in turn; the point is not that it is good but that it exists, which is exactly where $k\ge1$ is used.
--
--   **Formalization Note** `ServesFrom C₀ σ S` is the shared model's predicate for "the schedule `S` starts at `C₀` and serves `σ`". The statement is false for $k=0$ over a nonempty $M$, since no configuration of zero servers can cover a request.
-- source:
--   Model infrastructure for the offline optimum as defined in Manasse--McGeoch--Sleator, Competitive algorithms for server problems, J. Algorithms 11 (1990) 208-230, https://doi.org/10.1016/0196-6774(90)90003-W, Section 2 (the offline cost of a request sequence from a fixed initial configuration); the same definition is used in E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 2.

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem schedule_exists (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : ∃ S : ℕ → Config k M, ServesFrom C₀ σ S := by sorry

end KServer

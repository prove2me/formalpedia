-- Prove2me | Theorems.Thm_KServer_workFnU_mono
-- name    : KServer.workFnU_mono
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T06:57:06.660723+00:00
-- url     : https://prove2.me/theorems/6e91e3af-5658-44b4-a3de-325eb8344e41
-- title:
--   Serving one more request never decreases the unordered work function
-- statement:
--   Fix a metric space $M$, $k\ge1$ servers, an initial configuration $C_0$, a request sequence $\sigma$ and one further request $r$.
--
--   **Statement.** For every configuration $X$,
--   $$\widehat w_\sigma(X)\;\le\;\widehat w_{\sigma r}(X).$$
--
--   **Role.** The work function is nondecreasing in the request sequence: an offline solution serving $\sigma r$ also serves $\sigma$, so it competes in the smaller infimum. This is the fact that makes the increments $\widehat w_t(X)-\widehat w_{t-1}(X)$ nonnegative, and every bound on the *total* growth $\sum_t\max_X\{\widehat w_t(X)-\widehat w_{t-1}(X)\}$ — the quantity the Extended Cost Lemma converts into a competitive ratio — begins by using that sign. On a space of $k+1$ points, for instance, it is what lets the maximum over the $k+1$ possible holes be replaced by their sum, which then telescopes.
--
--   **Formalization Note** This is `KServer.workFn_mono` transported through the minimum over relabellings: a minimising permutation for the longer sequence is admissible for the shorter one.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, the third listed property of work functions; originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_mono (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    workFnU C₀ σ X ≤ workFnU C₀ (σ ++ [r]) X := by sorry

end KServer

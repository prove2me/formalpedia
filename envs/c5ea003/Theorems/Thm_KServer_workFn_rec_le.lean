-- Prove2me | Theorems.Thm_KServer_workFn_rec_le
-- name    : KServer.workFn_rec_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T05:18:33.316477+00:00
-- url     : https://prove2.me/theorems/6ce1666b-c207-461f-a9e3-1e64f8b577fe
-- title:
--   The work-function recurrence, upper half
-- statement:
--   For every server $i$,
--   $$w(C_0;\sigma\cdot r;X)\;\le\;w\bigl(C_0;\sigma;X[i\mapsto r]\bigr)+d\bigl(r,X_i\bigr),$$
--   where $X[i\mapsto r]$ denotes $X$ with server $i$ relocated to the request.
--
--   **Role.** This is the easy half of the work-function recurrence
--   $$w_t(X)=\min_{x\in X}\bigl\{w_{t-1}(X-x+r_t)+d(r_t,x)\bigr\},$$
--   the identity that allows the values of $w_t$ to be computed from those of $w_{t-1}$. The direction stated here is the one that exhibits a solution: end at $X$ with server $i$ parked on $r$, which serves the request, then walk that server back to its place in $X$. The converse half — that some server attains the minimum — is a separate statement.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, the properties of work functions listed after equation (4) (property 1, the upper bound); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunction

namespace KServer

theorem workFn_rec_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (i : Fin k) :
    workFn C₀ (σ ++ [r]) X ≤ workFn C₀ σ (Function.update X i r) + dist r (X i) := by sorry

end KServer

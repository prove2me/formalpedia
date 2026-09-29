-- Prove2me | Theorems.Thm_KServer_workFn_step_le
-- name    : KServer.workFn_step_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T06:14:03.043689+00:00
-- url     : https://prove2.me/theorems/03c4f2f9-8dca-473c-a1e1-a93349f8515f
-- title:
--   One step of the work-function recurrence, configuration form: upper half
-- statement:
--   Fix a metric space $M$, $k\ge1$ servers, an initial configuration $C_0$, a request sequence $\sigma$ and one further request $r$. Write $w_\sigma=w(C_0;\sigma;\cdot)$ for the work function after $\sigma$.
--
--   **Statement.** For every configuration $Y$ that covers $r$ (some server of $Y$ sits on $r$) and every configuration $Z$,
--   $$w_{\sigma r}(Z)\;\le\;w_\sigma(Y)+d(Y,Z).$$
--
--   **Role.** This is the *upper* half of the work function's one-step recurrence in **configuration form**,
--   $$w_{\sigma r}(Z)\;=\;\inf\{\,w_\sigma(Y)+d(Y,Z)\ :\ r\in Y\,\},$$
--   which is the form the Work Function Algorithm is defined by: at step $t$ the algorithm moves to a configuration containing $r_t$ that minimises $w_{t-1}(Y)+d(C_{t-1},Y)$, and the recurrence says that this minimum *is* $w_t(C_{t-1})$. That identification is the whole content of the characteristic equation $w_t(C_{t-1})=w_{t-1}(C_t)+d(C_{t-1},C_t)$ on which the analysis of the algorithm rests.
--
--   The proof is the direct one: an optimal schedule witnessing $w_\sigma(Y)$ is extended by one more configuration, namely $Y$ itself, which serves $r$; the extended schedule serves $\sigma r$, and its cost plus the final move to $Z$ is exactly the right-hand side.
--
--   **Formalization Note** The companion statement `KServer.workFn_step_approx` gives the matching lower half, with an $\varepsilon$ because on a general metric space the infimum need not be attained. This recurrence is the configuration-indexed sibling of `KServer.workFn_rec_le`/`KServer.workFn_rec_ge`, which are indexed instead by *which server* moves onto the request.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, equation (4) and the discussion of the Work Function Algorithm in Section 3.4 (the characteristic equation (7)); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunction

namespace KServer

theorem workFn_step_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (Z Y : Config k M) (hY : ∃ i, Y i = r) :
    workFn C₀ (σ ++ [r]) Z ≤ workFn C₀ σ Y + moveCost Y Z := by sorry

end KServer

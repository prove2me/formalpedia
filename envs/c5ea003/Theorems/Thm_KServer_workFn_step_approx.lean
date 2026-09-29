-- Prove2me | Theorems.Thm_KServer_workFn_step_approx
-- name    : KServer.workFn_step_approx
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T06:14:20.054342+00:00
-- url     : https://prove2.me/theorems/8c32d7fe-0c6a-4a43-8430-21d2c9c66bd0
-- title:
--   One step of the work-function recurrence, configuration form: lower half
-- statement:
--   Fix a metric space $M$, $k\ge1$ servers, an initial configuration $C_0$, a request sequence $\sigma$, one further request $r$, and a target configuration $Z$.
--
--   **Statement.** For every $\varepsilon>0$ there is a configuration $Y$ covering $r$ with
--   $$w_\sigma(Y)+d(Y,Z)\;\le\;w_{\sigma r}(Z)+\varepsilon .$$
--
--   **Role.** This is the *lower* half of the work function's one-step recurrence in configuration form,
--   $$w_{\sigma r}(Z)\;=\;\inf\{\,w_\sigma(Y)+d(Y,Z)\ :\ r\in Y\,\},$$
--   the half that says the infimum is not too large — every way of ending at $Z$ after serving $r$ passes through a configuration that covers $r$. The witness is read off an almost-optimal schedule for $w_{\sigma r}(Z)$: its configuration at the time $r$ is served covers $r$ by definition, and cutting the schedule there splits its cost into a part bounded by $w_\sigma(Y)$ and the final move.
--
--   Together with `KServer.workFn_step_le` this is what lets the Work Function Algorithm be *defined* on an arbitrary metric space: an exact minimiser of $w_{t-1}(Y)+d(C_{t-1},Y)$ over configurations containing $r_t$ need not exist when $M$ is not compact, but an $\varepsilon$-approximate one always does, and choosing $\varepsilon_t=2^{-t}$ makes the total slack at most $1$, which the additive constant of competitiveness absorbs.
--
--   **Formalization Note** The $\varepsilon$ is genuinely necessary: for an unbounded or open metric space the set $\{w_\sigma(Y)+d(Y,Z) : r\in Y\}$ can fail to contain its infimum. Every use of this lemma in the analysis of the Work Function Algorithm is compatible with a summable choice of $\varepsilon$.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, equation (4) and the discussion of the Work Function Algorithm in Section 3.4 (the characteristic equation (7)); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunction

namespace KServer

theorem workFn_step_approx (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (Z : Config k M) (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : Config k M, (∃ i, Y i = r) ∧
      workFn C₀ σ Y + moveCost Y Z ≤ workFn C₀ (σ ++ [r]) Z + ε := by sorry

end KServer

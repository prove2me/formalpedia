-- Prove2me | Theorems.Thm_KServer_workFnU_growth_card_add_two_start_inj
-- name    : KServer.workFnU_growth_card_add_two_start_inj
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-07T20:26:01.731492+00:00
-- url     : https://prove2.me/theorems/3ff22a35-9ec6-406b-85e4-b8837cc18db3
-- title:
--   Total growth $\le (k+1)\,\mathrm{OPT}$ at all configurations on $k+2$ points, injective start
-- statement:
--   Fix an initial configuration $C_0$ that occupies $k$ **distinct** points, and write $\widehat w_t=\widehat w(C_0;r_1,\dots,r_t;\cdot)$ for the unordered work function after the first $t$ requests of a sequence $\sigma$ of length $m$. Here $M$ is a metric space with exactly $k+2$ points, two more than the number of servers.
--
--   **Statement.** There is a constant $c$, depending on the metric space and on $C_0$ but not on the request sequence, such that for every $\sigma$ there are numbers $u_1,\dots,u_m$ with
--   $$\widehat w_t(X)\;\le\;\widehat w_{t-1}(X)+u_t\qquad\text{for \emph{every} configuration }X\text{ and every }t\le m,$$
--   $$\sum_{t=1}^{m}u_t\;\le\;(k+1)\cdot\mathrm{OPT}(C_0,\sigma)+c .$$
--
--   The bound is asked at every configuration $X:\mathrm{Fin}\,k\to M$, including degenerate ones that place two servers at the same point --- not only at the injective configurations for which the classical argument supplies it.
--
--   **Role.** This is the work-function content of the Koutsoupias--Papadimitriou theorem that the $k$-server conjecture holds on every metric space of $k+2$ points, proved there through the dual $2$-evader problem. By the Extended Cost Lemma the factor $k+1$ gives the ratio $k$. The injective form of this statement is `KServer.workFnU_growth_card_add_two_inj`.
--
--   **Why the injectivity hypothesis on $C_0$ appears.** For an injective start the work function is the largest $1$-Lipschitz extension of its restriction to injective configurations, so a growth bound proved at injective configurations transfers verbatim to all of them. This fails for a degenerate start: on the uniform three-point space with $k=2$ and $C_0=(p,p)$, the one-step growth at $(p,p)$ can exceed the growth at every injective configuration. The excess is then bounded by twice the distance from $C_0$ to the nearest injective configuration, but bounding the *total* excess over a long sequence requires an amortized argument that is not contained in this statement.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.4 (the Extended Cost Lemma and the work-function growth bounds, stated there for configurations as k-point sets). Original observation supplying the missing bridge between the set-valued classical formulation and the `Fin k -> M` formalization of this mission.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_growth_card_add_two_start_inj (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    [Fintype M] (hM : Fintype.card M = k + 2) (C₀ : Config k M)
    (hC₀ : Function.Injective C₀) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M,
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c := by sorry

end KServer

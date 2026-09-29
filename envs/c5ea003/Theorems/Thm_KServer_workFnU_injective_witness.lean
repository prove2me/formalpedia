-- Prove2me | Theorems.Thm_KServer_workFnU_injective_witness
-- name    : KServer.workFnU_injective_witness
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-07T20:25:51.078406+00:00
-- url     : https://prove2.me/theorems/b46d3ab6-082e-455c-80ca-266802927518
-- title:
--   For an injective start, the work function is the Lipschitz extension of its injective restriction
-- statement:
--   Fix a metric space $M$, a number $k\ge1$ of servers, and an initial configuration $C_0$ that occupies $k$ **distinct** points. For a request sequence $\sigma$ write $\widehat w_\sigma=\widehat w(C_0;\sigma;\cdot)$ for the unordered work function, and for configurations $X,Y$ write $\lVert X-Y\rVert=\sum_i d(X_i,Y_i)$ for the labelled movement cost.
--
--   **Statement.** For every $\sigma$, every configuration $Y$ and every $\varepsilon>0$ there is an *injective* configuration $X$ with
--   $$\widehat w_\sigma(X)+\lVert X-Y\rVert\;\le\;\widehat w_\sigma(Y)+\varepsilon .$$
--
--   Since the opposite inequality $\widehat w_\sigma(Y)\le\widehat w_\sigma(X)+\lVert X-Y\rVert$ is the Lipschitz property of the work function, the two together say
--   $$\widehat w_\sigma(Y)\;=\;\inf\{\,\widehat w_\sigma(X)+\lVert X-Y\rVert \;:\; X \text{ injective}\,\},$$
--   that is, the work function is the largest $1$-Lipschitz extension of its own restriction to injective configurations, and therefore carries no information at degenerate configurations beyond what it already carries at injective ones.
--
--   **Role.** The classical theory treats a configuration as a set of $k$ points, so degenerate configurations, which place two servers at a single point, do not occur in it. A formalization over maps $\mathrm{Fin}\,k\to M$ must deal with them, and the growth bounds of the work function are consequently available only in their injective form. This lemma is the bridge: any inequality between work functions that is proved at injective configurations and is preserved by the Lipschitz extension holds at every configuration.
--
--   **The hypothesis on $C_0$ is necessary.** On the uniform three-point space with $k=2$ and $C_0=(p,p)$, after the single request $p$ the work function vanishes at $(p,p)$, while every injective configuration lies at distance $1$ from it and has work-function value $1$; the right-hand side above equals $2$ and the statement fails by $2$. What survives for a degenerate start is the same statement with an additive slack equal to twice the distance from $C_0$ to the nearest injective configuration.
--
--   **Formalization note.** The error term $\varepsilon$ is present because on a general metric space the infimum over injective configurations need not be attained. The movement cost is the labelled one; this is the stronger reading, since the witness $X$ may be relabelled freely and `workFnU` is invariant under relabelling.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.4 (the Extended Cost Lemma and the work-function growth bounds, stated there for configurations as k-point sets). Original observation supplying the missing bridge between the set-valued classical formulation and the `Fin k -> M` formalization of this mission.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_injective_witness (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (hC₀ : Function.Injective C₀) (σ : List M) (Y : Config k M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X : Config k M, Function.Injective X ∧
      workFnU C₀ σ X + moveCost X Y ≤ workFnU C₀ σ Y + ε := by sorry

end KServer

-- Prove2me | Theorems.Thm_KServer_workFnU_growth_transfer_injective_start
-- name    : KServer.workFnU_growth_transfer_injective_start
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-07T20:25:29.961178+00:00
-- url     : https://prove2.me/theorems/b853bd0b-ea6c-4b6a-858f-078960eae4c0
-- title:
--   A work-function growth bound at injective configurations extends to all configurations
-- statement:
--   Fix a metric space $M$, $k\ge1$ servers, and an initial configuration $C_0$ occupying $k$ **distinct** points. Let $\sigma_1,\sigma_2$ be request sequences and $u\in\mathbb R$.
--
--   **Statement.** If
--   $$\widehat w_{\sigma_2}(X)\;\le\;\widehat w_{\sigma_1}(X)+u\qquad\text{for every \emph{injective} configuration }X,$$
--   then the same inequality holds for **every** configuration $X$, degenerate ones included.
--
--   **Role.** The work-function growth bounds that drive the $k$-server upper bounds --- the $3\,\mathrm{OPT}$ bound for two servers, the $(k+1)\,\mathrm{OPT}$ bound on spaces of $k+1$ and of $k+2$ points, and the $2k\,\mathrm{OPT}$ bound of Koutsoupias--Papadimitriou on general spaces --- are all of the form "one step of the work function grows by at most $u_t$ at every configuration", and their classical proofs give the bound only at configurations occupying $k$ distinct points. This principle upgrades any such bound to all configurations at once, so the two formulations coincide whenever the servers start at distinct points.
--
--   **Proof idea.** Given an arbitrary target $Y$ and $\varepsilon>0$, choose an injective $X$ with $\widehat w_{\sigma_1}(X)+\lVert X-Y\rVert\le\widehat w_{\sigma_1}(Y)+\varepsilon$, which is possible because for an injective start the work function is the Lipschitz extension of its injective restriction. Then
--   $$\widehat w_{\sigma_2}(Y)\;\le\;\widehat w_{\sigma_2}(X)+\lVert X-Y\rVert\;\le\;\widehat w_{\sigma_1}(X)+u+\lVert X-Y\rVert\;\le\;\widehat w_{\sigma_1}(Y)+u+\varepsilon,$$
--   using the Lipschitz property, then the hypothesis at $X$, then the choice of $X$; letting $\varepsilon\to0$ finishes.
--
--   **The hypothesis on $C_0$ is necessary**: for a degenerate start the conclusion acquires an additive slack proportional to the distance from $C_0$ to the nearest injective configuration.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.4 (the Extended Cost Lemma and the work-function growth bounds, stated there for configurations as k-point sets). Original observation supplying the missing bridge between the set-valued classical formulation and the `Fin k -> M` formalization of this mission.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_growth_transfer_injective_start (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (hC₀ : Function.Injective C₀) (σ₁ σ₂ : List M) (u : ℝ)
    (h : ∀ X : Config k M, Function.Injective X →
        workFnU C₀ σ₂ X ≤ workFnU C₀ σ₁ X + u) :
    ∀ X : Config k M, workFnU C₀ σ₂ X ≤ workFnU C₀ σ₁ X + u := by sorry

end KServer

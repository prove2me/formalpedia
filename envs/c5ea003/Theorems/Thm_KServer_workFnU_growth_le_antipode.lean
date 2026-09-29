-- Prove2me | Theorems.Thm_KServer_workFnU_growth_le_antipode
-- name    : KServer.workFnU_growth_le_antipode
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T05:40:14.225959+00:00
-- url     : https://prove2.me/theorems/cf5681f4-fcd3-4da8-a97f-2dd8de9c786e
-- title:
--   The extended cost is absorbed at the antipode of the request
-- statement:
--   Let $r$ be the next request of a $k$-server instance, in a metric space where $r$ has an **antipode**: a point $\bar r$ with
--
--   $$d(y, r) + d(y, \bar r) \;=\; 2\Delta \qquad \text{for every } y,$$
--
--   so that the whole space lies on geodesics from $r$ to $\bar r$. Then the one-request increase of the work function is maximised at the configuration $\bar r^{\,k}$ placing all $k$ servers at the antipode:
--
--   $$w_{\sigma r}(X) - w_\sigma(X) \;\le\; w_{\sigma r}(\bar r^{\,k}) - w_\sigma(\bar r^{\,k}) \qquad \text{for every configuration } X.$$
--
--   In other words, in a space with antipodes the **extended cost** $\max_X \bigl(w_{\sigma r}(X) - w_\sigma(X)\bigr)$ of a request is realised at a single canonical configuration determined by the request alone.
--
--   ## Why the antipode does it
--
--   The Koutsoupias--Papadimitriou duality lemma says the extended cost is attained at any minimiser of the dual functional $X \mapsto w_\sigma(X) - d(X, r^k)$. In general, locating such a minimiser is itself work. But when $r$ has an antipode, the defining identity turns the dual functional inside out: $d(X, r^k) = \sum_i d(x_i, r) = 2k\Delta - \sum_i d(x_i, \bar r) = 2k\Delta - d(X, \bar r^{\,k})$, so
--
--   $$w_\sigma(X) - d(X, r^k) \;=\; \bigl(w_\sigma(X) + d(X, \bar r^{\,k})\bigr) - 2k\Delta,$$
--
--   and minimising the right-hand side over $X$ is precisely what $1$-Lipschitzness of the work function does at the point $\bar r^{\,k}$: the minimum is $w_\sigma(\bar r^{\,k}) - 2k\Delta$, attained at $X = \bar r^{\,k}$. So the all-antipodes configuration is *automatically* a dual minimiser --- no structure of the space beyond the antipode identity, and no information about $w_\sigma$, is needed --- and duality hands over the conclusion.
--
--   ## Role
--
--   This is the mechanism by which the Coester--Koutsoupias potential controls the extended cost. Their potential anchored at $x_1, \dots, x_k$ ends with the summand $w(\bar x_k^{\,k})$; when the anchors can be chosen with $x_k = r$ the last summand is exactly $w(\bar r^{\,k})$, whose increase this theorem identifies as dominating the extended cost, while the remaining summands never decrease. The update property of the potential, hence $k$-competitiveness of the Work Function Algorithm through the potential criterion, thus reduces to showing the minimum of the potential is attained at anchors ending at the request --- which is the content of their per-space analyses (multi-ray spaces, trees, the circle). Applied inside the antipodal extension of an arbitrary space, where every point has an antipode by construction, the hypothesis is automatic.
--
--   ## Formalization note
--
--   The antipode enters only through the stated identity; no involution, no extension structure, and no bound on the other distances of the space are assumed. $\bar r^{\,k}$ is the constant configuration `fun _ => rbar`, and $w$ is `workFnU`, the work function of the unlabelled configuration.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, proof of Theorem 19 / Corollary 20: the change of the potential's last term bounds the extended cost, via the duality lemma of E. Koutsoupias, C. H. Papadimitriou, 'On the k-server conjecture', JACM 42 (1995), with the dual minimiser located at the antipode of the request.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_growth_le_antipode (k : ℕ) (hk : 1 ≤ k) (N : Type) [MetricSpace N]
    (C₀ : Config k N) (σ : List N) (r rbar : N) (Δ : ℝ)
    (hanti : ∀ y : N, dist y r + dist y rbar = 2 * Δ) (X : Config k N) :
    workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
      ≤ workFnU C₀ (σ ++ [r]) (fun _ => rbar) - workFnU C₀ σ (fun _ => rbar) := by sorry

end KServer

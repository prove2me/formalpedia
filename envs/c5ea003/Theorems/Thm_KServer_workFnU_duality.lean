-- Prove2me | Theorems.Thm_KServer_workFnU_duality
-- name    : KServer.workFnU_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:48:12.363209+00:00
-- url     : https://prove2.me/theorems/dae2c6a4-7906-45fe-85e1-4cbfce48f902
-- title:
--   The duality property of work functions
-- statement:
--   Fix a metric space $M$, $k\ge1$ servers, an initial configuration $C_0$, a request sequence $\sigma$ and one further request $r$. Write $\widehat w_{t-1}$ and $\widehat w_t$ for the unordered work functions before and after serving $r$, and let $d(r^k,X)=\sum_i d(r,X_i)$ be the total distance from $r$ to the points of $X$.
--
--   **Statement (duality).** Let $A$ be a **minimiser of $r$ with respect to $\widehat w_{t-1}$**, that is, a configuration minimising $\widehat w_{t-1}(X)-d(r^k,X)$. Then $A$ also minimises $\widehat w_t(X)-d(r^k,X)$, and it **maximises** $\widehat w_t(X)-\widehat w_{t-1}(X)$:
--   $$A\in\arg\min_X\bigl\{\widehat w_{t-1}(X)-d(r^k,X)\bigr\}\ \Longrightarrow\ A\in\arg\min_X\bigl\{\widehat w_{t}(X)-d(r^k,X)\bigr\}\ \text{ and }\ A\in\arg\max_X\bigl\{\widehat w_{t}(X)-\widehat w_{t-1}(X)\bigr\}.$$
--
--   **Role.** This is the property that carries the proof of the $(2k-1)$ bound. The Extended Cost Lemma reduces the competitive ratio of the Work Function Algorithm to a bound on the total growth $\sum_t\max_X\{\widehat w_t(X)-\widehat w_{t-1}(X)\}$; duality identifies exactly which configurations attain that maximum, and converts the quantity into a difference of minima,
--   $$\max_X\bigl\{\widehat w_t(X)-\widehat w_{t-1}(X)\bigr\}\;=\;\min_X\bigl\{\widehat w_t(X)-d(r^k,X)\bigr\}-\min_X\bigl\{\widehat w_{t-1}(X)-d(r^k,X)\bigr\},$$
--   which is the form the potential arguments of Koutsoupias and Papadimitriou operate on. The direction that needs duality is the one bounding the maximum from above; the reverse inequality is immediate from the definitions.
--
--   There is no evident intuition for why duality holds. It follows from the quasiconvexity of work functions (`KServer.workFnU_quasiconvex`), or from a similar but less straightforward parity argument on the two systems of paths.
--
--   **Formalization Note** Both conclusions are stated as universally quantified inequalities rather than as membership in an $\arg\min$, so that no existence of minimisers is asserted — on a general metric space they need not exist. The hypothesis is likewise conditional: it says only that *if* $A$ is such a minimiser, *then* the two conclusions hold. The quantity $d(r^k,X)$ is written `∑ i, dist r (X i)`, which is the minimum-cost matching between $X$ and the configuration consisting of $k$ copies of $r$.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, Lemma 1 (Duality property) and equation (5); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_duality (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (A : Config k M)
    (hA : ∀ X : Config k M,
      workFnU C₀ σ A - ∑ i, dist r (A i) ≤ workFnU C₀ σ X - ∑ i, dist r (X i)) :
    (∀ X : Config k M,
        workFnU C₀ (σ ++ [r]) A - ∑ i, dist r (A i)
          ≤ workFnU C₀ (σ ++ [r]) X - ∑ i, dist r (X i)) ∧
    (∀ X : Config k M,
        workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
          ≤ workFnU C₀ (σ ++ [r]) A - workFnU C₀ σ A) := by sorry

end KServer

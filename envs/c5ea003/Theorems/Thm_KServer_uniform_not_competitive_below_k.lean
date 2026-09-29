-- Prove2me | Theorems.Thm_KServer_uniform_not_competitive_below_k
-- name    : KServer.uniform_not_competitive_below_k
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-09T09:34:36.945008+00:00
-- url     : https://prove2.me/theorems/4c37a250-f345-455b-a618-0f28b4064dae
-- title:
--   Deterministic $k$-server: no algorithm is $c$-competitive for $c<k$ on the uniform space with $k+1$ points
-- statement:
--   **The competitive ratio of deterministic $k$-server algorithms is at least $k$.**
--
--   Let $k \ge 1$ and let $M$ be the *uniform* metric space on $k+1$ points: $M$ has exactly $k+1$ elements (witnessed by a bijection $e : \{0,\dots,k\} \to M$) and any two distinct points of $M$ are at distance $1$. This is the paging metric space with $k$ pages of cache and $k+1$ distinct pages.
--
--   Then no deterministic online $k$-server algorithm on $M$ is $c$-competitive for any $c < k$: for every algorithm $A$ and every additive constant $a$ there is a request sequence $\sigma$ with
--
--   $$\mathrm{cost}_A(\sigma) > c \cdot \mathrm{OPT}(\sigma) + a .$$
--
--   This is the classical lower bound of Manasse, McGeoch and Sleator: the adversary always requests the unique point not covered by the algorithm, so the algorithm pays $1$ per request, while an offline schedule that serves the requests in blocks of $k$ consecutive requests pays at most $n/k + k$ in total. It shows that the constant $k$ in the $k$-server conjecture is the smallest possible, so the conjecture — if true — is tight.
-- source:
--   M. S. Manasse, L. A. McGeoch, D. D. Sleator, Competitive algorithms for server problems, Journal of Algorithms 11 (1990) 208-230, Theorem 1 (lower bound k for any metric space with at least k+1 points).

import Definitions.Def_KServer_model

namespace KServer

theorem uniform_not_competitive_below_k (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (e : Fin (k + 1) ≃ M) (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (A : OnlineAlgorithm k M) (c : ℝ) (hc : c < k) :
    ¬ IsCompetitive A c := by sorry

end KServer

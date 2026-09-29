-- Prove2me | Theorems.Thm_KServer_competitive_lower_bound
-- name    : KServer.competitive_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:09:51.235182+00:00
-- url     : https://prove2.me/theorems/b7dbf9ab-9245-407a-be3e-75bca05e0c8c
-- title:
--   Lower bound: no deterministic algorithm beats ratio $k$
-- statement:
--   (Manasse--McGeoch--Sleator, 1990.) On any metric space containing at least $k+1$ distinct points, every $c$-competitive deterministic online $k$-server algorithm has $c \ge k$. Together with the conjectured upper bound this pins the deterministic competitive ratio at exactly $k$. The hypothesis of $k+1$ distinct points is necessary: on a space with at most $k$ points an algorithm can park servers on every point and be $0$-competitive.
-- source:
--   Manasse--McGeoch--Sleator, Competitive algorithms for server problems, J. Algorithms 11 (1990) 208-230, Corollary 7 (of Theorem 6): for any symmetric k-server problem there is no c-competitive algorithm for c < k, https://doi.org/10.1016/0196-6774(90)90003-W

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem competitive_lower_bound (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (hM : ∃ P : Finset M, P.card = k + 1)
    (A : OnlineAlgorithm k M) (c : ℝ) (hc : IsCompetitive A c) :
    (k : ℝ) ≤ c := by sorry

end KServer

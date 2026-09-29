-- Prove2me | Theorems.Thm_KServer_card_succ_competitive
-- name    : KServer.card_succ_competitive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:10:57.593039+00:00
-- url     : https://prove2.me/theorems/20cd875b-0599-4d21-9bc4-d2aa62c33d94
-- title:
--   The conjecture on spaces of $k+1$ points
-- statement:
--   (Manasse--McGeoch--Sleator, 1990.) On every finite metric space with exactly $k+1$ points there is a $k$-competitive deterministic online $k$-server algorithm from every initial configuration. With $k+1$ points exactly one point is uncovered at any time, which makes this the smallest nontrivial regime; it matches the lower bound, so the deterministic ratio on $(k+1)$-point spaces is exactly $k$.
-- source:
--   Manasse--McGeoch--Sleator, Competitive algorithms for server problems, J. Algorithms 11 (1990) 208-230, Theorem 4 and Corollary 8 (algorithm BAL is (n-1)-competitive for the (n-1)-server problem on n vertices), https://doi.org/10.1016/0196-6774(90)90003-W

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem card_succ_competitive (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    [Fintype M] (hM : Fintype.card M = k + 1) (C₀ : Config k M) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A (k : ℝ) := by sorry

end KServer

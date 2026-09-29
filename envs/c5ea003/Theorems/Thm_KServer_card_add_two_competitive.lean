-- Prove2me | Theorems.Thm_KServer_card_add_two_competitive
-- name    : KServer.card_add_two_competitive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:12:23.168924+00:00
-- url     : https://prove2.me/theorems/642b0d4b-34e0-457c-b337-dc050ed5a72d
-- title:
--   The conjecture on spaces of $k+2$ points
-- statement:
--   (Koutsoupias--Papadimitriou, 1996.) On every finite metric space with exactly $k+2$ points there is a $k$-competitive deterministic online $k$-server algorithm from every initial configuration. Equivalent, by duality, to the "$2$-evader problem"; together with the $(k+1)$-point case this is the strongest finite-cardinality regime in which the conjecture is known.
-- source:
--   Koutsoupias--Papadimitriou, The 2-evader problem, Information Processing Letters 57(5) (1996), 249--252, main theorem

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem card_add_two_competitive (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    [Fintype M] (hM : Fintype.card M = k + 2) (C₀ : Config k M) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A (k : ℝ) := by sorry

end KServer

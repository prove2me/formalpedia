-- Prove2me | Theorems.Thm_KServer_two_server_competitive
-- name    : KServer.two_server_competitive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:10:25.72138+00:00
-- url     : https://prove2.me/theorems/1691ef45-7b20-42f1-92ff-ce9779d5c239
-- title:
--   The conjecture for two servers
-- statement:
--   (Manasse--McGeoch--Sleator, 1990.) On every metric space and from every initial configuration there is a $2$-competitive deterministic online $2$-server algorithm — the $k$-server conjecture holds for $k = 2$. This was proved in the founding paper and remained for decades the only value of $k$ for which the conjecture was known on all metric spaces.
-- source:
--   Manasse--McGeoch--Sleator, Competitive algorithms for server problems, J. Algorithms 11 (1990) 208-230, Theorem 5 (algorithm RES is 2-competitive for the symmetric 2-server problem), proved there in the finite symmetric setting; cited for every metric space as the k=2 case of Conjecture 1.1 in Koutsoupias--Papadimitriou, J. ACM 42(5) (1995), Section 1; see also Chrobak--Larmore, The server problem and on-line games, DIMACS 1992 (Work Function Algorithm is 2-competitive for two servers)

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem two_server_competitive (M : Type) [MetricSpace M] (C₀ : Config 2 M) :
    ∃ A : OnlineAlgorithm 2 M, A.conf [] = C₀ ∧ IsCompetitive A 2 := by sorry

end KServer

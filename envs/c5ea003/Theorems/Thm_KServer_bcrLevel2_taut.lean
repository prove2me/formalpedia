-- Prove2me | Theorems.Thm_KServer_bcrLevel2_taut
-- name    : KServer.bcrLevel2_taut
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T13:55:18.617312+00:00
-- url     : https://prove2.me/theorems/ad00504d-367e-4035-bd51-cafc2cb26e8b
-- title:
--   Every level of the BCR space family is taut
-- statement:
--   **Every point of a level of the corrected BCR space family lies on a shortest path between the marked points.**
--
--   The space family of the Bubeck--Coester--Rabani lower bound is built by iterated theta gluing: level $0$ is the path of $\beta+1$ equally spaced points with the endpoints marked, and level $w+1$ glues two chains of three copies of level $w$ along their shared endpoints. The marked points of level $w$ are at distance $\beta\,3^{w}$.
--
--   A metric space with marked points $s \ne t$ is *taut* when
--
--   $$d(s,x) + d(x,t) \;=\; d(s,t) \qquad \text{for every point } x,$$
--
--   that is, when every point lies on a geodesic from $s$ to $t$. The statement asserts that every level of the family is taut. At level $0$ this is the identity $x + (\beta - x) = \beta$ on the path; at level $w+1$ both glued chains have length $3\,d_w(s_w,t_w)$, which is exactly the new distance between the marked points, so tautness is inherited from the level below.
--
--   **Role.** Tautness is a standing hypothesis of the level step of the construction, `KServer.level_step_sturdy` and `KServer.level_step_full`: it is what makes the escape price comparable with the distance and lets the geometric estimates of the race argument be carried out on the chain. Any recursion over the space family has to discharge it at every level, and this statement does so once and for all.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, https://arxiv.org/abs/2211.05753, Section 4 (the space M_w is a union of two geodesics between s_w and t_w); tautness hypothesis of the platform theorems KServer.level_step_sturdy and KServer.level_step_full, for the space family bcrLevel2.

import Mathlib
import Definitions.Def_KServer_chunk_system
import Definitions.Def_KServer_cycle_glue
import Definitions.Def_KServer_bcr_space
import Definitions.Def_KServer_glue2
import Definitions.Def_KServer_theta_dists
import Definitions.Def_KServer_race_geo
import Definitions.Def_KServer_bcr_space2

namespace KServer

theorem bcrLevel2_taut (β : ℕ) (hβ : 0 < β) (w : ℕ) (x : (bcrLevel2 β hβ w).carrier) :
    dist (bcrLevel2 β hβ w).s x + dist x (bcrLevel2 β hβ w).t
      = dist (bcrLevel2 β hβ w).s (bcrLevel2 β hβ w).t := by sorry

end KServer

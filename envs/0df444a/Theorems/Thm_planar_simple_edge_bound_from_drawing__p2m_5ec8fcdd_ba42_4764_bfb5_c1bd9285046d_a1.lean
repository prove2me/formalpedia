-- Prove2me | Theorems.Thm_planar_simple_edge_bound_from_drawing__p2m_5ec8fcdd_ba42_4764_bfb5_c1bd9285046d_a1
-- name    : planar_simple_edge_bound_from_drawing__p2m_5ec8fcdd_ba42_4764_bfb5_c1bd9285046d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:39:46.989541+00:00
-- url     : https://prove2.me/theorems/e3b94d84-a772-4bbe-8d1c-d23630bc7e79
-- title:
--   Simple planar graphs have at most 3V−6 edges
-- statement:
--   A finite connected simple graph on at least three vertices with a crossing-free drawing has at most three times its vertex count minus six edges. The additive form of the inequality avoids natural-number truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem planar_simple_edge_bound_from_drawing__p2m_5ec8fcdd_ba42_4764_bfb5_c1bd9285046d_a1 {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hHconn : H.Connected) (hHplanar : HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry

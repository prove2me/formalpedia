-- Prove2me | Theorems.Thm_planar_simple_edge_bound__p2m_07c458c9_4133_43a0_8b95_3696befe2c71_a1
-- name    : planar_simple_edge_bound__p2m_07c458c9_4133_43a0_8b95_3696befe2c71_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:24:29.397863+00:00
-- url     : https://prove2.me/theorems/c0996fde-699c-4c51-8b79-2ecab5268659
-- title:
--   Simple planar edge bound
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing has at most 3n − 6 edges. The connectedness hypothesis is retained to match the parent’s available assumptions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem planar_simple_edge_bound__p2m_07c458c9_4133_43a0_8b95_3696befe2c71_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hHconn : H.Connected) (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

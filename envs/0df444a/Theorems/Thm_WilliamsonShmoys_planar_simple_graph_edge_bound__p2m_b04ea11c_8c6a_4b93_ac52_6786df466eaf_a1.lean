-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_b04ea11c_8c6a_4b93_ac52_6786df466eaf_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_b04ea11c_8c6a_4b93_ac52_6786df466eaf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:55:07.32559+00:00
-- url     : https://prove2.me/theorems/37683aba-05a3-4c1a-ab3a-22541a69f955
-- title:
--   Edge bound for finite planar simple graphs
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_b04ea11c_8c6a_4b93_ac52_6786df466eaf_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hPlanar : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

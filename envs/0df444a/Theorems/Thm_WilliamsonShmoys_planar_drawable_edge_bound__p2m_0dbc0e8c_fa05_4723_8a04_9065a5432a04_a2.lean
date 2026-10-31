-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_bound__p2m_0dbc0e8c_fa05_4723_8a04_9065a5432a04_a2
-- name    : WilliamsonShmoys.planar_drawable_edge_bound__p2m_0dbc0e8c_fa05_4723_8a04_9065a5432a04_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:37:22.981754+00:00
-- url     : https://prove2.me/theorems/9786a817-f7aa-4876-b28c-017cd5fca12a
-- title:
--   Edge bound for any graph with a planar drawing
-- statement:
--   Every finite simple graph on at least three vertices with a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawable_edge_bound__p2m_0dbc0e8c_fa05_4723_8a04_9065a5432a04_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

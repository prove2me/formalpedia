-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_bound__p2m_40bf128a_95fa_481c_8fd2_3c8143f624ef_a2
-- name    : WilliamsonShmoys.maximal_drawable_edge_bound__p2m_40bf128a_95fa_481c_8fd2_3c8143f624ef_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:18:58.633785+00:00
-- url     : https://prove2.me/theorems/0dbc0e8c-fa05-4723-8a04-9065a5432a04
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_drawable_edge_bound__p2m_40bf128a_95fa_481c_8fd2_3c8143f624ef_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hMax : ∀ N : SimpleGraph V, H ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ H) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

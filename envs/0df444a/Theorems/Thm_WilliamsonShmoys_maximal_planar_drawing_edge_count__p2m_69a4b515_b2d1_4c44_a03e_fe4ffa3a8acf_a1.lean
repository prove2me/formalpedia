-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_69a4b515_b2d1_4c44_a03e_fe4ffa3a8acf_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_69a4b515_b2d1_4c44_a03e_fe4ffa3a8acf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:08.187764+00:00
-- url     : https://prove2.me/theorems/f80cfa01-1746-4a4f-be01-21a16939b3a9
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable graph maximal under inclusion among drawable supergraphs on the same finite vertex type, with at least three vertices, has exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_69a4b515_b2d1_4c44_a03e_fe4ffa3a8acf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

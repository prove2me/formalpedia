-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph__p2m_8c6de935_4f5b_49ef_8949_a6af2a37957f_a1
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_8c6de935_4f5b_49ef_8949_a6af2a37957f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:15:50.746488+00:00
-- url     : https://prove2.me/theorems/2facc1d9-8574-46e5-b6ec-a0ba2784b822
-- title:
--   Planar graph extends to a triangulated planar supergraph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. Such a supergraph is obtained by extending the drawing to a triangulation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_8c6de935_4f5b_49ef_8949_a6af2a37957f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

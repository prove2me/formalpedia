-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_triangulated_edge_count__p2m_e0e04b13_f360_445e_bd9a_b3847171c53c_a1
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_e0e04b13_f360_445e_bd9a_b3847171c53c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:27:35.832483+00:00
-- url     : https://prove2.me/theorems/0d90a4e2-211c-41d9-a3e6-1089ea8087c9
-- title:
--   Complete a planar drawing to the triangulation edge count
-- statement:
--   Every finite planar graph on at least three vertices has a planar supergraph on the same vertex set with exactly 3|V|−6 edges. This is the triangulation-completion step; it also covers disconnected input graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_e0e04b13_f360_445e_bd9a_b3847171c53c_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry

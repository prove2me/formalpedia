-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_9ec06c2a_4897_4f0a_9340_6489b642dcd9_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_9ec06c2a_4897_4f0a_9340_6489b642dcd9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:54:48.812181+00:00
-- url     : https://prove2.me/theorems/971f615d-fe0b-4924-8df8-81bd7d133755
-- title:
--   Complete a finite plane graph to a triangulated supergraph
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex set with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_9ec06c2a_4897_4f0a_9340_6489b642dcd9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    exists K : SimpleGraph V, G <= K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry

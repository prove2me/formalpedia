-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_2aad9942_4caf_404d_a0f5_d5621274176b_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_2aad9942_4caf_404d_a0f5_d5621274176b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:48:48.22742+00:00
-- url     : https://prove2.me/theorems/b707ad4a-77a6-470e-9bb1-a016cbfcb978
-- title:
--   Planar drawing extends to a triangulation
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices can be extended, using the same vertices, to a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_2aad9942_4caf_404d_a0f5_d5621274176b_a1 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

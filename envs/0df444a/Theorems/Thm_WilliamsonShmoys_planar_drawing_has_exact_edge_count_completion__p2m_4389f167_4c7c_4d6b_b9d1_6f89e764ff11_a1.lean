-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_4389f167_4c7c_4d6b_b9d1_6f89e764ff11_a1
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_4389f167_4c7c_4d6b_b9d1_6f89e764ff11_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:29:56.976133+00:00
-- url     : https://prove2.me/theorems/14aa0c9f-f5a1-4cc0-8732-cecb86e5e8ad
-- title:
--   Completion of a planar drawing to the maximal edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices is contained in a drawable graph on the same vertices with exactly 3|V|−6 edges. This completion lemma removes the topological and counting work from the parent; maximality then identifies the completion with the original graph. A proof route is to choose a drawable supergraph with maximal edge count, establish that its faces are triangular, and combine Euler’s formula with face-edge incidence counting. At |V|=3, the completion is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_4389f167_4c7c_4d6b_b9d1_6f89e764ff11_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

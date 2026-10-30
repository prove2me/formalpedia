-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_00e8ebb5_9f6a_4f3b_a13c_8345d9aaf556_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_00e8ebb5_9f6a_4f3b_a13c_8345d9aaf556_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T01:02:11.607849+00:00
-- url     : https://prove2.me/theorems/a712b8ac-2693-4359-b1bf-8163c9ce4446
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An edge-inclusion-maximal graph with the supplied planar drawing property and at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_00e8ebb5_9f6a_4f3b_a13c_8345d9aaf556_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K → H.edgeSet = K.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry

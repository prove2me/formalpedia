-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T21:44:09.971344+00:00
-- url     : https://prove2.me/theorems/3fec8f0c-c3a7-4eba-b2f0-d2b6c5de2dde
-- title:
--   A maximal drawable simple graph has the Euler edge count
-- statement:
--   A drawable finite simple graph on at least three vertices that has no proper drawable supergraph on the same vertex type has exactly three times the number of vertices minus six edges. Maximality yields a connected triangulation; Euler’s formula and the face-degree count give the equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

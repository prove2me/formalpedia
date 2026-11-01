-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:15:36.039379+00:00
-- url     : https://prove2.me/theorems/8bcf31fc-0140-4078-86ae-c40cd3c611a4
-- title:
--   Edge bound for a maximal planar drawing
-- statement:
--   A maximal crossing-free drawing on at least three vertices has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel H.Adj := Classical.decRel _
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry

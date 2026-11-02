-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound__p2m_701795bb_5022_4e86_97bf_b07b90c6661c_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_701795bb_5022_4e86_97bf_b07b90c6661c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:25:07.419206+00:00
-- url     : https://prove2.me/theorems/6f9002e1-e01e-4c8a-bc92-8342a46a38e8
-- title:
--   Edge bound for an edge-maximal planar graph
-- statement:
--   A finite simple graph on at least three vertices that is maximal among planar supergraphs on the same vertex type has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_701795bb_5022_4e86_97bf_b07b90c6661c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K ≤ H)
    [DecidableRel H.Adj] :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry

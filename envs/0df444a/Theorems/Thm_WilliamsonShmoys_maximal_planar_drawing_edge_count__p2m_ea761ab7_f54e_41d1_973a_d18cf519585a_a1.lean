-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_ea761ab7_f54e_41d1_973a_d18cf519585a_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_ea761ab7_f54e_41d1_973a_d18cf519585a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T12:40:36.740486+00:00
-- url     : https://prove2.me/theorems/8be6e20d-20e4-4a9a-97eb-8181cc85f42c
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A connected drawable graph with at least three vertices that is maximal among drawable supergraphs on the same vertex set has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_ea761ab7_f54e_41d1_973a_d18cf519585a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hmax : ∀ M : SimpleGraph V,
      K.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

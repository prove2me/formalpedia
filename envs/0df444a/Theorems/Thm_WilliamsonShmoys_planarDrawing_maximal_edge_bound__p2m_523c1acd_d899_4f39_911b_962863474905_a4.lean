-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_maximal_edge_bound__p2m_523c1acd_d899_4f39_911b_962863474905_a4
-- name    : WilliamsonShmoys.planarDrawing_maximal_edge_bound__p2m_523c1acd_d899_4f39_911b_962863474905_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T00:31:06.289462+00:00
-- url     : https://prove2.me/theorems/d61162a7-4b41-4107-8a03-73f62fd7affc
-- title:
--   Edge bound for a maximum-edge planar drawing
-- statement:
--   A drawable graph with at least three vertices that has maximum edge count among its drawable supergraphs satisfies the planar triangulation edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_maximal_edge_bound__p2m_523c1acd_d899_4f39_911b_962863474905_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hP : HasPlanarDrawingOn P)
    (hCard : 3 <= Fintype.card V)
    (hMax : ∀ Q : SimpleGraph V, P <= Q → HasPlanarDrawingOn Q →
      Q.edgeSet.ncard <= P.edgeSet.ncard) :
    3 * Fintype.card V <= P.edgeSet.ncard + 6 := by sorry

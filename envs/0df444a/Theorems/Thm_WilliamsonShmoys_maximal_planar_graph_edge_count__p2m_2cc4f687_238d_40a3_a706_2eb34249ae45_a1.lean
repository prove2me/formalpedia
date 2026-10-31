-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_2cc4f687_238d_40a3_a706_2eb34249ae45_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_2cc4f687_238d_40a3_a706_2eb34249ae45_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:37:45.561202+00:00
-- url     : https://prove2.me/theorems/3beca25f-dcd0-483c-98b9-d914f407e162
-- title:
--   An inclusion-maximal drawable graph has exactly 3n−6 edges
-- statement:
--   A graph on at least three vertices with the supplied planar drawing, maximal among drawable supergraphs on the same vertex type, has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_2cc4f687_238d_40a3_a706_2eb34249ae45_a1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry

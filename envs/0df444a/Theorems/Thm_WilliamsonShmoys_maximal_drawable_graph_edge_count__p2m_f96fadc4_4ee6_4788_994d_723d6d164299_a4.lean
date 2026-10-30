-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_f96fadc4_4ee6_4788_994d_723d6d164299_a4
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_f96fadc4_4ee6_4788_994d_723d6d164299_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:56:49.767819+00:00
-- url     : https://prove2.me/theorems/7592409d-0b44-4594-9ed9-df868002d7c4
-- title:
--   Maximal drawable graphs have the maximal planar edge count
-- statement:
--   For a finite simple graph with at least three vertices, a crossing-free drawing and maximality among drawable graphs on the same vertex type imply that three times the vertex count equals the edge count plus six. This is the classical maximal-planar edge-count formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_f96fadc4_4ee6_4788_994d_723d6d164299_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset H.edgeSet K.edgeSet ->
      H.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V = H.edgeSet.ncard + 6 := by sorry

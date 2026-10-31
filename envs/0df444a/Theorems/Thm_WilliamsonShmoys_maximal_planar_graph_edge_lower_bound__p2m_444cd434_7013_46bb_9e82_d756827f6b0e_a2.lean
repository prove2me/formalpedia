-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_444cd434_7013_46bb_9e82_d756827f6b0e_a2
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_444cd434_7013_46bb_9e82_d756827f6b0e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:19:46.092525+00:00
-- url     : https://prove2.me/theorems/77d34f95-c28b-41e7-bbec-f475d739e777
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A graph with a crossing-free drawing that is maximal among drawable graphs on the same vertex set has at least 3|V| − 6 edges when there are at least three vertices. Extend the drawing to a triangulation on the same vertices; maximality forces the extension to have the original edge set, and a triangulation has 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_444cd434_7013_46bb_9e82_d756827f6b0e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      K.edgeFinset ⊆ L.edgeFinset ->
      WilliamsonShmoys.HasPlanarDrawingOn L ->
      L.edgeFinset = K.edgeFinset) :
    3 * Fintype.card V - 6 <= K.edgeFinset.card := by sorry

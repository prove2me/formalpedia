-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_b83083f9_5b98_4643_9156_0c35319b256b_a2
-- name    : WilliamsonShmoys.planar_completion_edge_count__p2m_b83083f9_5b98_4643_9156_0c35319b256b_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:40:48.406571+00:00
-- url     : https://prove2.me/theorems/9fe93ea1-3ec4-44e7-b185-a82282fa7ec5
-- title:
--   Completion of a drawable graph to a triangulation edge count
-- statement:
--   Any drawable finite simple graph on at least three vertices can be extended on the same vertex set to a drawable graph with exactly three times the number of vertices minus six edges. The child also returns the edge-set finiteness instance required by Mathlib’s edgeFinset definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_edge_count__p2m_b83083f9_5b98_4643_9156_0c35319b256b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ (hKfin : Fintype K.edgeSet),
        (letI : Fintype K.edgeSet := hKfin
         3 * Fintype.card V = K.edgeFinset.card + 6) := by
  sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_20261027
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_20261027
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T20:33:11.460984+00:00
-- url     : https://prove2.me/theorems/caef8af6-6bb5-4457-a7a2-5f5411524f81
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A planar graph on at least three vertices that maximizes the number of edges among its planar supergraphs on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ H.edgeSet.ncard) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

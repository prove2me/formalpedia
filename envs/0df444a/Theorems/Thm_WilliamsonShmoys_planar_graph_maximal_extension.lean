-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_maximal_extension
-- name    : WilliamsonShmoys.planar_graph_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:22:27.892836+00:00
-- url     : https://prove2.me/theorems/2ad0e69f-16da-4ec3-9f11-488b1304720b
-- title:
--   Extend a connected planar drawing to an edge-maximal planar graph
-- statement:
--   Extend the given connected graph, without changing its vertex type, to a graph that is maximal under edge inclusion among graphs admitting the specified crossing-free drawing. Connectivity and the vertex-count bound are retained as hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      (∀ K : SimpleGraph V, HasPlanarDrawingOn K →
        (∀ u v, H.Adj u v → K.Adj u v) →
        ∀ u v, K.Adj u v → H.Adj u v) := by sorry

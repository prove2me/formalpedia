-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_exact_edge_supergraph
-- name    : WilliamsonShmoys.planar_graph_has_exact_edge_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T09:27:09.071996+00:00
-- url     : https://prove2.me/theorems/dd73cac9-b90d-44a4-8977-1c0859414274
-- title:
--   Planar graph extends to an exact-edge planar supergraph
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices is contained in a graph on the same vertex type that has a crossing-free drawing and exactly `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_exact_edge_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

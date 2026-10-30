-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_bound_for_edge_maximal_graph
-- name    : WilliamsonShmoys.planar_edge_augmentation_below_bound_for_edge_maximal_graph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:06:20.790457+00:00
-- url     : https://prove2.me/theorems/2f17cb44-8508-4651-b167-c84d8482efa9
-- title:
--   Planar edge augmentation below the triangulation bound
-- statement:
--   If a finite simple planar graph on at least three vertices has fewer than 3|V|−6 edges, then it has a planar supergraph on the same vertex type with strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_below_bound_for_edge_maximal_graph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcount : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ M : SimpleGraph V,
      G.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      G.edgeSet.ncard < M.edgeSet.ncard := by sorry

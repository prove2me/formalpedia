-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_edge_maximal_supergraph_20261026
-- name    : WilliamsonShmoys.planar_graph_has_edge_maximal_supergraph_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:15:33.518695+00:00
-- url     : https://prove2.me/theorems/cf5d3579-fb92-4602-b735-00aa5ffc6ef6
-- title:
--   Finite edge-maximal planar supergraph
-- statement:
--   Every finite graph with a crossing-free drawing has a planar supergraph on the same vertex type that has no strict planar supergraph on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_edge_maximal_supergraph_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ J : SimpleGraph V,
        K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = K := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_edge_count
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:26:48.186435+00:00
-- url     : https://prove2.me/theorems/b54e7d04-48fd-4e8e-8887-2e9c417d6f73
-- title:
--   Planar completion with the maximal planar edge count
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three is a subgraph of a graph on the same vertices with a crossing-free drawing and exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

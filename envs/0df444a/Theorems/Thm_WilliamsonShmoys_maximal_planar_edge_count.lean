-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count
-- name    : WilliamsonShmoys.maximal_planar_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:20:32.318782+00:00
-- url     : https://prove2.me/theorems/32d86918-6982-4733-a1e2-a3bf2cc7c17b
-- title:
--   A maximal planar graph has three times the vertex count minus six edges
-- statement:
--   For a finite planar graph on at least three vertices, if every planar supergraph on the same vertices is already a subgraph of it, then its edge count is three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry

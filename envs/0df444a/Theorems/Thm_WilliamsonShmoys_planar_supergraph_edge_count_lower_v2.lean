-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_v2
-- name    : WilliamsonShmoys.planar_supergraph_edge_count_lower_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:11:49.135167+00:00
-- url     : https://prove2.me/theorems/e419c2ea-e7eb-49d6-8d1d-4e46e6428aa2
-- title:
--   Planar supergraph with the maximal planar edge count
-- statement:
--   Every graph with a drawing witness has, on the same vertex type, a drawable supergraph with at least 3|V|−6 edges when the vertex count is at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_supergraph_edge_count_lower_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L ≤ M ∧
      3 * (Fintype.card V : Int) - 6 <= (M.edgeSet.ncard : Int) := by sorry

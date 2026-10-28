-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_exact_edge_count
-- name    : WilliamsonShmoys.planar_supergraph_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:44:06.572688+00:00
-- url     : https://prove2.me/theorems/d91007ea-2b83-4647-90f6-3b32f55c223e
-- title:
--   Planar supergraph completion with exact edge count
-- statement:
--   Every finite planar graph with at least three vertices is a subgraph of a planar graph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, L.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

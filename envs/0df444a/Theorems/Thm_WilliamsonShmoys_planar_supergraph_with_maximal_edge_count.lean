-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_maximal_edge_count
-- name    : WilliamsonShmoys.planar_supergraph_with_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:21:12.176474+00:00
-- url     : https://prove2.me/theorems/a9181169-d523-4da1-8834-b734217e5ad6
-- title:
--   Planar supergraph with maximal edge count
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has a crossing-free supergraph on the same vertex set with exactly 3n−6 edges. The parent applies maximality to this supergraph to identify it with the original graph and obtain the target bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_with_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, HasPlanarDrawingOn T ∧
      (∀ u v, G.Adj u v → T.Adj u v) ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

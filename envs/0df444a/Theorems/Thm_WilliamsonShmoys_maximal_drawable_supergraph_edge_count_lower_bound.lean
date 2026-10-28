-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count_lower_bound
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_edge_count_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T23:42:57.167982+00:00
-- url     : https://prove2.me/theorems/81618fe6-49b7-47ea-89df-6c1a8f23fc25
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V, W ≤ X →
      WilliamsonShmoys.HasPlanarDrawingOn X → X = W) :
    3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by
  sorry

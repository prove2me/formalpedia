-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_drawable_supergraph_card_repair_20261027
-- name    : WilliamsonShmoys.edge_maximal_drawable_supergraph_card_repair_20261027
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T21:18:41.319157+00:00
-- url     : https://prove2.me/theorems/5ac0c4f7-6455-4ae4-ac3e-220b84c3380a
-- title:
--   Maximum-edge drawable supergraphs have triangulation size
-- statement:
--   A drawable supergraph with maximum edge count among drawable supergraphs of W has exactly 3n−6 edges when V has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_drawable_supergraph_card_repair_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (U : SimpleGraph V)
    (hWU : W ≤ U)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ H : SimpleGraph V, W ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H →
      H.edgeSet.ncard ≤ U.edgeSet.ncard) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

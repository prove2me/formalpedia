-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_dense_supergraph_ctx816e1e7
-- name    : WilliamsonShmoys.planar_drawing_dense_supergraph_ctx816e1e7
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:48:50.804561+00:00
-- url     : https://prove2.me/theorems/0d608879-4556-44b4-bb66-f079ed5049f3
-- title:
--   Drawable graphs have a dense drawable supergraph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type whose edge count is at least 3|V| − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_dense_supergraph_ctx816e1e7
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    exists S : SimpleGraph V,
      R <= S /\ WilliamsonShmoys.HasPlanarDrawingOn S /\
        3 * Fintype.card V <= S.edgeSet.ncard + 6 := by
  sorry

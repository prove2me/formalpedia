-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_ctx816e1e7
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_ctx816e1e7
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:37:12.284019+00:00
-- url     : https://prove2.me/theorems/331b3b22-eabb-488b-9457-bd3d4254a18e
-- title:
--   Maximal planar edge lower bound for this target
-- statement:
--   An inclusion-maximal simply drawable graph with at least three vertices has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_ctx816e1e7
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : forall S : SimpleGraph V, R <= S ->
      WilliamsonShmoys.HasPlanarDrawingOn S -> S <= R) :
    3 * Fintype.card V <= R.edgeSet.ncard + 6 := by sorry

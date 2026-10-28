-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_ctx816e1e7a
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_ctx816e1e7a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:05:18.508524+00:00
-- url     : https://prove2.me/theorems/c72a9a05-e87e-4fe2-b1e7-8c96278e5fc9
-- title:
--   An inclusion-maximal planar graph has at least 3n minus 6 edges
-- statement:
--   An inclusion-maximal planar graph on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_ctx816e1e7a
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ U : SimpleGraph V, W < U → ¬ WilliamsonShmoys.HasPlanarDrawingOn U) :
    3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by sorry

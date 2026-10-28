-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_lower_bound_16efa91f_ea17_4fca_8681_329f091064c3
-- name    : WilliamsonShmoys.maximal_drawing_edge_lower_bound_16efa91f_ea17_4fca_8681_329f091064c3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:34:06.262381+00:00
-- url     : https://prove2.me/theorems/8e593656-efe4-4618-ae6d-cce680220389
-- title:
--   Lower edge bound for a maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_edge_lower_bound_16efa91f_ea17_4fca_8681_329f091064c3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    3 * Fintype.card V - 6 <= M.edgeSet.ncard := by sorry

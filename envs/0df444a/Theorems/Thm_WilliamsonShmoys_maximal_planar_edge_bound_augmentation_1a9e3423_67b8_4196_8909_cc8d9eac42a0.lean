-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_augmentation_1a9e3423_67b8_4196_8909_cc8d9eac42a0
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_augmentation_1a9e3423_67b8_4196_8909_cc8d9eac42a0
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:03:04.175561+00:00
-- url     : https://prove2.me/theorems/2fefb580-d0d8-475e-846e-4a87a5492af7
-- title:
--   A drawable graph has a drawable supergraph with the planar edge lower bound
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound_augmentation_1a9e3423_67b8_4196_8909_cc8d9eac42a0
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V,
      G ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧
        3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by sorry

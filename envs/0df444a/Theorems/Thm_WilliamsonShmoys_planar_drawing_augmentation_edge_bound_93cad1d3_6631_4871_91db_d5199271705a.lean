-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_edge_bound_93cad1d3_6631_4871_91db_d5199271705a
-- name    : WilliamsonShmoys.planar_drawing_augmentation_edge_bound_93cad1d3_6631_4871_91db_d5199271705a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:57:15.777327+00:00
-- url     : https://prove2.me/theorems/1016eb9f-955e-4666-8793-89a9a11ff9b9
-- title:
--   Augment a planar drawing to the planar edge bound
-- statement:
--   For any drawable simple graph on a finite linearly ordered vertex type with at least three vertices, there is a drawable supergraph on the same vertices whose number of edges is at least 3|V| − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_augmentation_edge_bound_93cad1d3_6631_4871_91db_d5199271705a
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V <= L.edgeSet.ncard + 6 := by sorry

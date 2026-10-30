-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_augmentation_edge_bound
-- name    : WilliamsonShmoys.planar_drawingOn_augmentation_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:24:03.153579+00:00
-- url     : https://prove2.me/theorems/d0745305-c146-4fb8-be9e-fcbd8df8567a
-- title:
--   Drawable graphs admit an edge-dense drawable augmentation
-- statement:
--   Every finite graph with at least three vertices and a drawing satisfying the exact `HasPlanarDrawingOn` predicate has a drawable supergraph on the same vertex type with at least `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawingOn_augmentation_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V, T ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧
      3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by sorry

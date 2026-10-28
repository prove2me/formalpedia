-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_edge_lower
-- name    : WilliamsonShmoys.planar_drawing_augmentation_edge_lower
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:27:56.638421+00:00
-- url     : https://prove2.me/theorems/c2692e15-4304-47c5-864b-198ffa7f5189
-- title:
--   Planar drawings admit an edge-rich supergraph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_augmentation_edge_lower
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      U <= W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      3 * Fintype.card V <= W.edgeSet.ncard + 6 := by sorry

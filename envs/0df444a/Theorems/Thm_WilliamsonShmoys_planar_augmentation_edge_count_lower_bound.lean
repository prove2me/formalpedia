-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_count_lower_bound
-- name    : WilliamsonShmoys.planar_augmentation_edge_count_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:24:48.846997+00:00
-- url     : https://prove2.me/theorems/856388c3-d7a3-49dc-acab-0480aa762444
-- title:
--   Planar graphs admit a dense drawable extension
-- statement:
--   For every drawable simple graph on at least three vertices, there is a drawable supergraph on the same vertex type with at least 3n − 6 edges. The child preserves the original edges; it does not assume the input graph is connected or maximal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V, W.edgeSet ⊆ X.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      3 * Fintype.card V ≤ X.edgeSet.ncard + 6 := by sorry

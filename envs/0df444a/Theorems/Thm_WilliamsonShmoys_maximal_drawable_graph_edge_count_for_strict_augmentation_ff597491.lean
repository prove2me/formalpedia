-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_for_strict_augmentation_ff597491
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_for_strict_augmentation_ff597491
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:53:39.088832+00:00
-- url     : https://prove2.me/theorems/c683258d-9797-470e-9da6-8cc1d2b584e1
-- title:
--   Edge count of a maximal drawable graph for strict augmentation
-- statement:
--   A drawable graph on at least three vertices with no strictly larger drawable supergraph has exactly `3n − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_for_strict_augmentation_ff597491 {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V) (hUdraw : WilliamsonShmoys.HasPlanarDrawingOn U) (hCard : 3 ≤ Fintype.card V) (hUmax : ∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = U) : U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

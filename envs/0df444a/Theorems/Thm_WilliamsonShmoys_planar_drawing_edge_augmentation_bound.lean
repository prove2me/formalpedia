-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation_bound
-- name    : WilliamsonShmoys.planar_drawing_edge_augmentation_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:55:49.056015+00:00
-- url     : https://prove2.me/theorems/b426a2d2-76fa-4962-9a0d-98aaf5e77c76
-- title:
--   Planar drawing admits an edge-rich augmentation
-- statement:
--   Every graph with the specified crossing-free drawing and at least three vertices is contained in a graph on the same vertex type that has such a drawing and at least 3|V|−6 edges. This child removes the planar-topology work from the parent: triangulation and Euler counting prove the edge bound, while the parent uses maximality to identify the augmentation with the original graph. Its hypotheses cover the n=3 boundary case and preserve the exact drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_augmentation_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ U : SimpleGraph V,
      G ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧
        3 * Fintype.card V - 6 ≤ U.edgeSet.ncard := by sorry

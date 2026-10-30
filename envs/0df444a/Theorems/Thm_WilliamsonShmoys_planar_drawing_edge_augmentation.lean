-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation
-- name    : WilliamsonShmoys.planar_drawing_edge_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:15:31.052569+00:00
-- url     : https://prove2.me/theorems/bb833034-0d51-4ffd-859f-1866e5737dc6
-- title:
--   A sparse planar drawing admits an edge augmentation
-- statement:
--   On at least three vertices, if a graph has a crossing-free drawing and fewer than 3|V|−6 edges, then some strictly larger graph on the same vertices also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hsmall : Z.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ W : SimpleGraph V,
      Z < W ∧ WilliamsonShmoys.HasPlanarDrawingOn W := by sorry

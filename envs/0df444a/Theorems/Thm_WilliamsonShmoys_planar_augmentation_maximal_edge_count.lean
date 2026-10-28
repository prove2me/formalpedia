-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_maximal_edge_count
-- name    : WilliamsonShmoys.planar_augmentation_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:38:45.086958+00:00
-- url     : https://prove2.me/theorems/2982080e-3c6e-4528-958e-70cfb6fd3a9c
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal under drawable edge-preserving extension has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hmax : ∀ Y : SimpleGraph V, X.edgeSet ⊆ Y.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn Y → Y.edgeSet ⊆ X.edgeSet) :
    3 * Fintype.card V ≤ X.edgeSet.ncard + 6 := by sorry

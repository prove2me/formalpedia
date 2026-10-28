-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_of_sparse
-- name    : WilliamsonShmoys.planar_edge_augmentation_of_sparse
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:14:49.140859+00:00
-- url     : https://prove2.me/theorems/395ae7cf-6cd3-4191-8701-f181061f6644
-- title:
--   Sparse planar graph admits a planar edge augmentation
-- statement:
--   For a finite ordered vertex type with at least three vertices, any graph with a crossing-free planar drawing and fewer than 3|V|−6 edges has a strictly larger planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_of_sparse
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hsparse : H.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ G : SimpleGraph V, H <= G ∧ G ≠ H ∧ WilliamsonShmoys.HasPlanarDrawingOn G := by sorry

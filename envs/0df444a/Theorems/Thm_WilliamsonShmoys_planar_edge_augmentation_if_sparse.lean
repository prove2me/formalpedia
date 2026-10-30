-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_if_sparse
-- name    : WilliamsonShmoys.planar_edge_augmentation_if_sparse
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:08:38.368928+00:00
-- url     : https://prove2.me/theorems/fd0d87e6-b805-416b-90da-57eb1ca5807e
-- title:
--   Sparse drawable graphs admit a strict drawable augmentation
-- statement:
--   For at least three vertices, any graph with a crossing-free drawing and fewer than 3|V|−6 edges has a crossing-free strict supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_if_sparse
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hsparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ ¬ M ≤ L := by sorry

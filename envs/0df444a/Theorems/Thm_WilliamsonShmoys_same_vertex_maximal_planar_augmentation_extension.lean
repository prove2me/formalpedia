-- Prove2me | Theorems.Thm_WilliamsonShmoys_same_vertex_maximal_planar_augmentation_extension
-- name    : WilliamsonShmoys.same_vertex_maximal_planar_augmentation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:34:33.09307+00:00
-- url     : https://prove2.me/theorems/b8cea6f3-68c6-4015-982f-6b7fec31d201
-- title:
--   Maximal planar extension on the same vertex set
-- statement:
--   A planar graph on a finite ordered vertex type with at least three vertices has an inclusion-maximal planar supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.same_vertex_maximal_planar_augmentation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry

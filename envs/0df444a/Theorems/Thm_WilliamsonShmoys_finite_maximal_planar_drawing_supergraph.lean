-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_drawing_supergraph
-- name    : WilliamsonShmoys.finite_maximal_planar_drawing_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:46:34.366547+00:00
-- url     : https://prove2.me/theorems/da081504-86c7-4ca6-a27b-d2e67a7a59c0
-- title:
--   A finite planar drawing has an inclusion-maximal drawable supergraph
-- statement:
--   Among the finitely many simple graphs on V that contain H and have a drawing, choose one with the largest edge set. It is inclusion-maximal. The assertion also covers the smallest allowed vertex set; no assumption about connectedness is needed. This removes the existence-of-a-maximal-extension step from the parent, without relying on topological edge augmentation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_planar_drawing_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  sorry

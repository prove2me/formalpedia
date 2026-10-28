-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension_finite
-- name    : WilliamsonShmoys.planar_drawable_maximal_extension_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:21:35.724852+00:00
-- url     : https://prove2.me/theorems/8a65547d-33a5-417d-96fe-2722dbcbbb2b
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable graph on the given finite vertex type has a drawable supergraph maximal among drawable supergraphs on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_maximal_extension_finite
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L →
          WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  sorry

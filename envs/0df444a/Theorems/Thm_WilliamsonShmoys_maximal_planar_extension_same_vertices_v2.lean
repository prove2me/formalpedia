-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_same_vertices_v2
-- name    : WilliamsonShmoys.maximal_planar_extension_same_vertices_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:59:49.605692+00:00
-- url     : https://prove2.me/theorems/e6ae682c-f6d3-4d99-9106-0c83b8640c97
-- title:
--   Maximal planar extension on the same finite vertex set
-- statement:
--   Every finite graph with a drawing in the plane has an inclusion-maximal drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension_same_vertices_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V, H ≤ K →
          WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry

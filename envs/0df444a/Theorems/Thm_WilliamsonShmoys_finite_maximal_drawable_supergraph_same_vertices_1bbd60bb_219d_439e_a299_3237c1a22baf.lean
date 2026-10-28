-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph_same_vertices_1bbd60bb_219d_439e_a299_3237c1a22baf
-- name    : WilliamsonShmoys.finite_maximal_drawable_supergraph_same_vertices_1bbd60bb_219d_439e_a299_3237c1a22baf
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:55:35.318875+00:00
-- url     : https://prove2.me/theorems/bfd20f24-dbb7-4853-94fd-cd51c0915373
-- title:
--   Finite maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on that same vertex type that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_drawable_supergraph_same_vertices_1bbd60bb_219d_439e_a299_3237c1a22baf
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M →
          WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry

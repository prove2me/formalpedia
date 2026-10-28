-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_exists_maximal_drawable_supergraph
-- name    : WilliamsonShmoys.planar_extension_exists_maximal_drawable_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:17:08.687758+00:00
-- url     : https://prove2.me/theorems/b0de8d28-78bd-4941-bf7d-fa7c16729377
-- title:
--   Every drawable graph has a maximal drawable supergraph
-- statement:
--   Every graph with a planar drawing on a finite vertex type is contained in a drawable graph with no strictly larger drawable supergraph on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_exists_maximal_drawable_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V, U ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
      ∀ Z : SimpleGraph V, W ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z ≤ W := by sorry

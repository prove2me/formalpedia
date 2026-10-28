-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_repair_543ac5d4
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_repair_543ac5d4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:05:05.797426+00:00
-- url     : https://prove2.me/theorems/1f8870b8-c241-419b-8fb0-22dc12f06ebb
-- title:
--   Finite maximal drawable supergraph for the repair
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that is maximal among drawable supergraphs on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_repair_543ac5d4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ U : SimpleGraph V,
      G <= U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      ∀ W : SimpleGraph V,
        U <= W →
        WilliamsonShmoys.HasPlanarDrawingOn W →
        W = U := by sorry

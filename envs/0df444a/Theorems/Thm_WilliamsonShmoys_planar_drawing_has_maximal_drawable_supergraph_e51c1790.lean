-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_drawable_supergraph_e51c1790
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_drawable_supergraph_e51c1790
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:02:58.181336+00:00
-- url     : https://prove2.me/theorems/ab72dd67-69d0-4720-8860-4a32405da0cd
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_drawable_supergraph_e51c1790
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      ∀ W : SimpleGraph V,
        U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = U := by sorry

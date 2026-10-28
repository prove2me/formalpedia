-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_dense_supergraph_choose_maximal
-- name    : WilliamsonShmoys.planar_drawing_dense_supergraph_choose_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:49:49.421679+00:00
-- url     : https://prove2.me/theorems/cd39200c-229a-4644-a937-4360c64be7b2
-- title:
--   Choose a maximal drawable supergraph
-- statement:
--   For a finite vertex type, every graph with the supplied planar drawing has a drawable supergraph that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_dense_supergraph_choose_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry

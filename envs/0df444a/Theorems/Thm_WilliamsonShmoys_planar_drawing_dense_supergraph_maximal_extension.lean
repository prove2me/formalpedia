-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_dense_supergraph_maximal_extension
-- name    : WilliamsonShmoys.planar_drawing_dense_supergraph_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:56:33.92699+00:00
-- url     : https://prove2.me/theorems/ea3f2cf9-6031-4c69-a7b3-74aa9f7a4039
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Extend any drawable finite simple graph on at least three vertices to a drawable supergraph on the same vertex type that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_dense_supergraph_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    exists S : SimpleGraph V,
      R <= S /\ WilliamsonShmoys.HasPlanarDrawingOn S /\
        (forall T : SimpleGraph V,
          S <= T -> WilliamsonShmoys.HasPlanarDrawingOn T -> T <= S) := by
  sorry

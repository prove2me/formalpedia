-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph_c2692e15_4304_47c5_864b_198ffa7f5189
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_c2692e15_4304_47c5_864b_198ffa7f5189
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:38:40.442893+00:00
-- url     : https://prove2.me/theorems/fb644066-e521-417c-8bc6-77c501d87aeb
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   A drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_c2692e15_4304_47c5_864b_198ffa7f5189
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      U ≤ W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      ∀ Z : SimpleGraph V, W ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z ≤ W := by sorry

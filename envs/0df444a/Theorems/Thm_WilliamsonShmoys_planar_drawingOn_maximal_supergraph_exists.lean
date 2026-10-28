-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_supergraph_exists
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_supergraph_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:39:59.423981+00:00
-- url     : https://prove2.me/theorems/8d2f099d-df6a-4dfd-b4c9-6872d6341c05
-- title:
--   Finite edge-maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type has a drawable supergraph on the same vertices that has no drawable strict supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_maximal_supergraph_exists
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ T : SimpleGraph V, Z ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T := by sorry

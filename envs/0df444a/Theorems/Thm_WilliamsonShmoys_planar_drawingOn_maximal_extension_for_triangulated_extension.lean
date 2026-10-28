-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_for_triangulated_extension
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_extension_for_triangulated_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:01:28.292765+00:00
-- url     : https://prove2.me/theorems/ddf8e4da-a17e-4c60-a4c8-4da5ba7a393b
-- title:
--   Finite maximal drawable supergraph for triangulated extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under graph inclusion. Choose a graph with the greatest number of edges among drawable supergraphs; any proper drawable supergraph would have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_maximal_extension_for_triangulated_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry

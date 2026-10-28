-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_200a044f_248b_4fd0_bcd3_c7e9d499ee78
-- name    : WilliamsonShmoys.maximal_planar_edge_count_200a044f_248b_4fd0_bcd3_c7e9d499ee78
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:47:27.878594+00:00
-- url     : https://prove2.me/theorems/a0f6bf19-8587-4855-98af-5f8973796e56
-- title:
--   A maximal drawable graph has the maximal planar edge count
-- statement:
--   If a drawable graph on at least three vertices has no strictly larger drawable supergraph on the same vertex type, then it has exactly 3|V| − 6 edges. Maximality forces a connected triangulation; Euler’s formula and counting face-edge incidences give the equality, with the three-vertex boundary case handled directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_200a044f_248b_4fd0_bcd3_c7e9d499ee78
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V,
      T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V = T.edgeSet.ncard + 6 := by
  sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_47cfe247_f32d_4afb_b363_54161b3a97c2
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_47cfe247_f32d_4afb_b363_54161b3a97c2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:55:38.753199+00:00
-- url     : https://prove2.me/theorems/9f08b824-8932-4d56-9a90-925f5b8e07cc
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable graphs on the same vertex type has at least `3 * |V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_bound_47cfe247_f32d_4afb_b363_54161b3a97c2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry

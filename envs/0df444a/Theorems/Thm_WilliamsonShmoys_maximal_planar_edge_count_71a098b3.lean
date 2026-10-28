-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_71a098b3
-- name    : WilliamsonShmoys.maximal_planar_edge_count_71a098b3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:53:14.774295+00:00
-- url     : https://prove2.me/theorems/5de28ece-d44b-4081-bf2d-b88716525470
-- title:
--   Maximal drawable graphs have the planar edge count
-- statement:
--   A drawable simple graph that is maximal among drawable simple graphs on its vertex set, with at least three vertices, has exactly `3 * |V| - 6` edges. The proof route establishes that maximality forces a triangulation and applies Euler’s formula, with the three-vertex case included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_71a098b3 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) (hcard : 3 ≤ Fintype.card V) : 3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry

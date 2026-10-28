-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_le_three_n_sub_six_from_planar_drawing
-- name    : WilliamsonShmoys.edge_count_le_three_n_sub_six_from_planar_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:51:18.357467+00:00
-- url     : https://prove2.me/theorems/5438d717-60ba-4719-bd8d-a39b0e45c967
-- title:
--   Planar Euler edge-count upper bound
-- statement:
--   A finite simple graph with the supplied planar drawing and at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_le_three_n_sub_six_from_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry

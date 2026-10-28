-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_of_drawing
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_of_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:32:49.011111+00:00
-- url     : https://prove2.me/theorems/8398ec67-a394-4cc8-8745-77d07baaa8e2
-- title:
--   Planar edge count upper bound
-- statement:
--   Every finite simple graph on at least three vertices with a crossing-free drawing has at most 3|V|−6 edges. The proof route is the planar Euler formula, with the small-face cases handled using simplicity and the at-least-three-vertices hypothesis. This removes the upper-bound half of the target from the parent proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_of_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

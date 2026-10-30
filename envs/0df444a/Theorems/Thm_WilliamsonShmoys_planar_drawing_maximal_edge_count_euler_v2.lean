-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_count_euler_v2
-- name    : WilliamsonShmoys.planar_drawing_maximal_edge_count_euler_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:29:37.618656+00:00
-- url     : https://prove2.me/theorems/96423339-d6c7-499e-a706-076681b42078
-- title:
--   Euler edge count for maximal drawable graphs
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3n−6 edges. This isolates the topological and Euler-counting argument used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_edge_count_euler_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

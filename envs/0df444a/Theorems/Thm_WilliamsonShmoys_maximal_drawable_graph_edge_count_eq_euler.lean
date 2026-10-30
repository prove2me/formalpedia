-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_eq_euler
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_eq_euler
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:14:15.303701+00:00
-- url     : https://prove2.me/theorems/fd4411d1-6686-4dd0-8ebd-1fd40ccbea70
-- title:
--   Maximal drawable graphs have the Euler edge count
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_eq_euler
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry

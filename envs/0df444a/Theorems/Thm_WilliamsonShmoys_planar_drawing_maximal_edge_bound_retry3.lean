-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_bound_retry3
-- name    : WilliamsonShmoys.planar_drawing_maximal_edge_bound_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:06:27.188268+00:00
-- url     : https://prove2.me/theorems/7bc1289d-8327-434b-91d8-bc8bc37c92c5
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_edge_bound_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

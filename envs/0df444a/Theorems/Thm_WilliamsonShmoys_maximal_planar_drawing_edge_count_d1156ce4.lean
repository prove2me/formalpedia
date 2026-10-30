-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_d1156ce4
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_d1156ce4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:42:34.347294+00:00
-- url     : https://prove2.me/theorems/c8ef0a28-b308-4db5-8ad2-c1274e7c4a15
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A maximal simple graph with a crossing-free drawing and at least three vertices has exactly 3|V|−6 edges. This child handles the plane-topology and edge-counting argument; combined with the parent’s Euler-count hypothesis, it yields the target incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_d1156ce4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : forall J : SimpleGraph V, H <= J -> HasPlanarDrawingOn J -> J = H)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V = H.edgeSet.ncard + 6 := by sorry

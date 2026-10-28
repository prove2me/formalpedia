-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_from_euler_c132589d_retry3
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_from_euler_c132589d_retry3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T23:17:15.3845+00:00
-- url     : https://prove2.me/theorems/e5800fef-fc2c-4e78-bbf0-8dfb83fed07a
-- title:
--   Planar drawing edge bound from Euler's formula
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_from_euler_c132589d_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

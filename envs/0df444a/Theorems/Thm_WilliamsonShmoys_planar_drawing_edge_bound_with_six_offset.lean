-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_with_six_offset
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_with_six_offset
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:25:26.138277+00:00
-- url     : https://prove2.me/theorems/0d94eccd-1b7d-4473-b0bf-957d45668280
-- title:
--   Planar drawings satisfy the three-n-minus-six edge bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_with_six_offset
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : HasPlanarDrawingOn W)
    (hCard : 3 ≤ Fintype.card V) :
    W.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

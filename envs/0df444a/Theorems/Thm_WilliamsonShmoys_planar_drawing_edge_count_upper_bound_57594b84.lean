-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_57594b84
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound_57594b84
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:54:32.065416+00:00
-- url     : https://prove2.me/theorems/dab997b7-011a-464b-8944-eb16bc367747
-- title:
--   Planar drawing edge count upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3n−6 edges. This isolates the Euler edge bound from maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound_57594b84
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

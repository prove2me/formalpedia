-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_repair3
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_repair3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:44:51.274272+00:00
-- url     : https://prove2.me/theorems/b3dae40e-180e-47db-8e40-863b2716c108
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every graph with a crossing-free drawing on at least three finite vertices has at most `3 * |V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHdraw : HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry

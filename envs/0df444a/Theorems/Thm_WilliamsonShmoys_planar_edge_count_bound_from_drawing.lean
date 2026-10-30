-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_from_drawing
-- name    : WilliamsonShmoys.planar_edge_count_bound_from_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:40:00.043+00:00
-- url     : https://prove2.me/theorems/3cc4cf7f-7032-42f1-b72a-a5e5ef47d140
-- title:
--   Edge bound for a finite planar drawing
-- statement:
--   Every finite simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V| − 6 edges, without any maximality assumption.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_bound_from_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

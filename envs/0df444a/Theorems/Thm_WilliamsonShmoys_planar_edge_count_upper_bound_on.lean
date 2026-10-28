-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_on
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_on
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T20:18:48.841983+00:00
-- url     : https://prove2.me/theorems/97deac54-3db7-4d8c-ac09-4329b922220c
-- title:
--   Planar edge count upper bound on a fixed vertex set
-- statement:
--   Every graph with the specified planar drawing on at least three finite ordered vertices has at most three times its vertex count minus six edges. The boundary n = 3 is included; the inequality is valid even for disconnected graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_on
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

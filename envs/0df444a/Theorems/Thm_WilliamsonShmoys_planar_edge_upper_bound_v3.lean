-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_v3
-- name    : WilliamsonShmoys.planar_edge_upper_bound_v3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T19:26:27.318509+00:00
-- url     : https://prove2.me/theorems/4aa7f655-933d-4eaf-8c8b-78c708788d37
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A graph with a crossing-free drawing on a finite ordered vertex type with at least three vertices has at most `3|V| − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

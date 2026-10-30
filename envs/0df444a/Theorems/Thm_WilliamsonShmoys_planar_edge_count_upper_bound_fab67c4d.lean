-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_fab67c4d
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_fab67c4d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:55:24.893244+00:00
-- url     : https://prove2.me/theorems/a3e41bac-cf3e-4358-b96a-889e9698cdb0
-- title:
--   Planar drawing edge upper bound
-- statement:
--   A finite simple graph with the specified planar drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_fab67c4d
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    (L.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry

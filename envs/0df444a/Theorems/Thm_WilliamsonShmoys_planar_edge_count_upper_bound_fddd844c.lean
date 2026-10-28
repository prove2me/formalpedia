-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_fddd844c
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_fddd844c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:53:09.298354+00:00
-- url     : https://prove2.me/theorems/3d7100f8-80c0-4f0e-a27d-3a5c94ab2f10
-- title:
--   Planar edge-count upper bound for the assigned theorem
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_fddd844c
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    (M.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry

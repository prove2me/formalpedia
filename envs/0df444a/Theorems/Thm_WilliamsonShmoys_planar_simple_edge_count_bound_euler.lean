-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_count_bound_euler
-- name    : WilliamsonShmoys.planar_simple_edge_count_bound_euler
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:22:53.207842+00:00
-- url     : https://prove2.me/theorems/63531e10-8ad4-4ca6-8cf0-a029bc134469
-- title:
--   Euler upper bound for a simply drawn planar graph
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_edge_count_bound_euler
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

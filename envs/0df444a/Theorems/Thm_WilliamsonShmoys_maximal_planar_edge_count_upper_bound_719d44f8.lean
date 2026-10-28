-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound_719d44f8
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper_bound_719d44f8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:55:49.40621+00:00
-- url     : https://prove2.me/theorems/df291747-b13b-4c14-8629-f80551fb9437
-- title:
--   Euler upper bound for an embedded simple graph
-- statement:
--   For at least three vertices, every graph with the supplied crossing-free arc drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count_upper_bound_719d44f8
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry

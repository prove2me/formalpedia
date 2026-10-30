-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_for_maximal_planar_edge_count_by_triangulation_65d9599f
-- name    : WilliamsonShmoys.planar_edge_upper_bound_for_maximal_planar_edge_count_by_triangulation_65d9599f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:31:41.981986+00:00
-- url     : https://prove2.me/theorems/394777ae-ca5b-4f9d-b6a6-4b9523b3e67c
-- title:
--   Planar edge upper bound for the triangulation count
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound_for_maximal_planar_edge_count_by_triangulation_65d9599f
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_v2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:45:43.973766+00:00
-- url     : https://prove2.me/theorems/d2c60fb0-0563-43d4-b001-f44ca2f3ff38
-- title:
--   Euler edge bound for a planar simple graph
-- statement:
--   Every simple graph with a crossing-free drawing on at least three vertices has at most 3|V|−6 edges. This supplies the upper-bound half of the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    Q.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry

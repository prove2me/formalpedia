-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_e5c3d806_69b9_4602_a0f9_34c482daacc9
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_e5c3d806_69b9_4602_a0f9_34c482daacc9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:51:52.973529+00:00
-- url     : https://prove2.me/theorems/42ccc764-2657-424e-8d6b-03a01aecd866
-- title:
--   Planar simple graphs satisfy the Euler edge bound
-- statement:
--   Every drawable simple graph with at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_e5c3d806_69b9_4602_a0f9_34c482daacc9
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hV : 3 ≤ Fintype.card V) :
    Z.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry

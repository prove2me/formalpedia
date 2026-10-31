-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_13694d57_9c40_45ab_89d1_4e7bf234d7f8_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_13694d57_9c40_45ab_89d1_4e7bf234d7f8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:10:14.788442+00:00
-- url     : https://prove2.me/theorems/c769ec5a-3e49-48b5-92c4-83cb5745da0c
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   For a finite simple graph with a planar drawing and at least three vertices, the edge count is at most 3n−6. A proof can use Euler’s formula and the fact that face boundaries in a suitable connected augmentation have length at least three, while accounting for disconnected components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_13694d57_9c40_45ab_89d1_4e7bf234d7f8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry

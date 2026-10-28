-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T22:14:29.684226+00:00
-- url     : https://prove2.me/theorems/a3da1208-9df8-43b8-bead-079a944eccc6
-- title:
--   Planar edge-count upper bound for a finite drawing
-- statement:
--   A graph on at least three vertices with the specified crossing-free drawing has at most `3|V| - 6` edges, whether or not it is connected. This removes the edge-count upper-bound argument from the parent. A proof route is to establish Euler’s formula and the face-degree bound for each component, then combine the component bounds while preserving the stated `|V| ≥ 3` condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

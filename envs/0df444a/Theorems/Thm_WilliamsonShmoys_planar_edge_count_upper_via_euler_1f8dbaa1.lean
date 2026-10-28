-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_via_euler_1f8dbaa1
-- name    : WilliamsonShmoys.planar_edge_count_upper_via_euler_1f8dbaa1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:36:28.406746+00:00
-- url     : https://prove2.me/theorems/74303e8f-7c9c-49a8-919b-9d949dc96169
-- title:
--   Euler upper bound for a finite drawable simple graph
-- statement:
--   Every finite simple graph with the supplied crossing-free drawing and at least three vertices has at most `3|V| - 6` edges. The proof route uses Euler’s formula and face boundary counts, with a component-joining step for disconnected graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_via_euler_1f8dbaa1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_c5c6f6ee
-- name    : WilliamsonShmoys.planar_edge_upper_bound_c5c6f6ee
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:46:51.575667+00:00
-- url     : https://prove2.me/theorems/29d68590-8ef2-48f9-a26d-7cd75ba497d4
-- title:
--   Planar drawing edge upper bound
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3n − 6 edges. This is the standard planar Euler edge bound. It removes the universal upper-bound part of the target. A proof route is to pass from the drawing to a planar embedding, apply Euler’s formula componentwise or by a suitable planar augmentation, and use simplicity to bound face lengths. The n = 3 boundary case is retained.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound_c5c6f6ee
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

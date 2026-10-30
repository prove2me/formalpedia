-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:28:39.629969+00:00
-- url     : https://prove2.me/theorems/d8a399ef-5b7d-46cc-b52a-cc9763228ec4
-- title:
--   Simple planar edge-count upper bound
-- statement:
--   A simple graph with a crossing-free drawing on at least three vertices has at most `3n − 6` edges. This supplies the upper bound needed to turn maximality into an exact edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry

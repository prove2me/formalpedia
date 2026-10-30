-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_repair_543ac5d4
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_repair_543ac5d4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:37:41.432899+00:00
-- url     : https://prove2.me/theorems/094f9761-81cb-4254-a465-084cbfd6a9aa
-- title:
--   Planar edge-count upper bound for the repair
-- statement:
--   Every graph with a crossing-free drawing on at least three finite ordered vertices has at most `3|V| - 6` edges. The proof route is componentwise: use Euler's formula and face-boundary incidence counting on components of size at least three, bound size-one and size-two components directly, then sum. The small-component cases and the global `|V| ≥ 3` boundary are necessary when the drawing is disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_repair_543ac5d4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry

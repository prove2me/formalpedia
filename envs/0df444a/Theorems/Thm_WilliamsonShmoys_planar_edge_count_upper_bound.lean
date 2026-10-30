-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:43:06.841862+00:00
-- url     : https://prove2.me/theorems/6d462b53-1ad0-496d-b2a6-6fc80fdec20e
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every graph on at least three vertices admitting the specified crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry

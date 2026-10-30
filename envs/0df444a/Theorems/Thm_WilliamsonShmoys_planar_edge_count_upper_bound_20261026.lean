-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_20261026
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:51:31.329979+00:00
-- url     : https://prove2.me/theorems/f7de7f15-66ff-47e1-b746-2eefed596e80
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every simply drawn planar graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    J.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry

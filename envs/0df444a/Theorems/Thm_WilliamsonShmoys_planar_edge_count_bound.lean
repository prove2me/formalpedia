-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound
-- name    : WilliamsonShmoys.planar_edge_count_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:06:08.062007+00:00
-- url     : https://prove2.me/theorems/88f16e45-08da-4474-bad8-5a6b999a0a9f
-- title:
--   Planar edge-count upper bound
-- statement:
--   A drawable simple graph on at least three vertices has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_d16397ab_f97b_4b48_8e65_cb91b43850d6_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_d16397ab_f97b_4b48_8e65_cb91b43850d6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:40.805325+00:00
-- url     : https://prove2.me/theorems/009c4248-3452-48fd-902a-fcf77cc64290
-- title:
--   Planar graph edge-count upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The bound includes disconnected drawings; the usual proof applies Euler’s formula componentwise and handles isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_d16397ab_f97b_4b48_8e65_cb91b43850d6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  sorry

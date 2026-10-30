-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_98c8bf31_da7f_4753_99f2_642509315647_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_98c8bf31_da7f_4753_99f2_642509315647_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T18:37:25.609762+00:00
-- url     : https://prove2.me/theorems/1080ccf9-69ad-46ce-852f-7faab6d5860a
-- title:
--   Euler upper bound for planar edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices has at most 3|V|−6 edges. This follows from Euler’s formula and planar face counting, with disconnected components and small faces handled in the standard bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_98c8bf31_da7f_4753_99f2_642509315647_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry

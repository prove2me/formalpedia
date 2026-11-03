-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_e592f479_7758_40c0_97f7_ee5e29c0fee3_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_e592f479_7758_40c0_97f7_ee5e29c0fee3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:24:52.176417+00:00
-- url     : https://prove2.me/theorems/8348399b-8cb6-45dd-ab73-26e7cc43a44d
-- title:
--   Drawable graphs satisfy the planar edge upper bound
-- statement:
--   A graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_e592f479_7758_40c0_97f7_ee5e29c0fee3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry

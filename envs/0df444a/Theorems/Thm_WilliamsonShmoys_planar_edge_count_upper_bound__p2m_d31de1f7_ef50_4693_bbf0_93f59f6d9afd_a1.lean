-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
-- name    : WilliamsonShmoys_planar_edge_count_upper_bound__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:11:29.52339+00:00
-- url     : https://prove2.me/theorems/1313175c-9801-43ac-98ea-21e1b7fe79cc
-- title:
--   Planar edge count upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_planar_edge_count_upper_bound__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry

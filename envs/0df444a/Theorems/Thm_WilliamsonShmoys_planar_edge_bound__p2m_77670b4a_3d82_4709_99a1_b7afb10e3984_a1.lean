-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_77670b4a_3d82_4709_99a1_b7afb10e3984_a1
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_77670b4a_3d82_4709_99a1_b7afb10e3984_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T23:55:45.02876+00:00
-- url     : https://prove2.me/theorems/8c35848a-12bf-457f-86fe-ab0dfb66c1ed
-- title:
--   Edge bound for a finite planar drawing
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound__p2m_77670b4a_3d82_4709_99a1_b7afb10e3984_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry

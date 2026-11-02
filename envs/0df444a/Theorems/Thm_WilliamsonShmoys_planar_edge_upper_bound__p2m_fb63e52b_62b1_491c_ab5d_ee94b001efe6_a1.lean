-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_fb63e52b_62b1_491c_ab5d_ee94b001efe6_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_fb63e52b_62b1_491c_ab5d_ee94b001efe6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:19:07.560956+00:00
-- url     : https://prove2.me/theorems/48fd94ac-39d1-4989-ad8e-5c8896a37126
-- title:
--   Euler upper bound for a planar simple graph
-- statement:
--   For a finite simple graph with at least three vertices and a crossing-free drawing as specified by HasPlanarDrawingOn, the number of edges is at most 3|V| − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_fb63e52b_62b1_491c_ab5d_ee94b001efe6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry

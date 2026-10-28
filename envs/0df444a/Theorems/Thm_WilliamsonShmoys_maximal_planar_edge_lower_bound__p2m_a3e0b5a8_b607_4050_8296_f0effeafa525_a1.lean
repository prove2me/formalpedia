-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_a3e0b5a8_b607_4050_8296_f0effeafa525_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_a3e0b5a8_b607_4050_8296_f0effeafa525_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:36:54.691707+00:00
-- url     : https://prove2.me/theorems/70d53a58-d41a-4eac-ac1b-1d93346406ec
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has at least three times its vertex count minus six edges. The proof route is to show that maximality forces every face to be triangular, then combine face-edge incidence counting with Euler’s formula. At three vertices the bound is zero, and the complete triangle attains equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_a3e0b5a8_b607_4050_8296_f0effeafa525_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry

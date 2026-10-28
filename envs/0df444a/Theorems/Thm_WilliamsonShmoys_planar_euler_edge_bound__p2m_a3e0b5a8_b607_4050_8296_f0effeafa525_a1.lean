-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_euler_edge_bound__p2m_a3e0b5a8_b607_4050_8296_f0effeafa525_a1
-- name    : WilliamsonShmoys.planar_euler_edge_bound__p2m_a3e0b5a8_b607_4050_8296_f0effeafa525_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:36:59.129076+00:00
-- url     : https://prove2.me/theorems/761eb288-0e8b-41fc-9ae8-379c5de8c950
-- title:
--   Euler equation and edge upper bound for a maximal drawable graph
-- statement:
--   For a maximal drawable simple graph on at least three vertices, there is a face count satisfying Euler’s equation, and its edge count is at most three times the vertex count minus six. Maximality is included because it ensures the graph is connected, as required for this Euler equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open SimpleGraph

theorem WilliamsonShmoys.planar_euler_edge_bound__p2m_a3e0b5a8_b607_4050_8296_f0effeafa525_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_triangulated_planar_graph__p2m_5897f64b_d93f_46d0_b145_4fa00606e1c1_a3
-- name    : WilliamsonShmoys.exists_connected_triangulated_planar_graph__p2m_5897f64b_d93f_46d0_b145_4fa00606e1c1_a3
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T02:22:01.073364+00:00
-- url     : https://prove2.me/theorems/1a209498-2a51-4cd7-9b09-dd65c1d25569
-- title:
--   A connected planar graph attaining the planar edge bound
-- statement:
--   On every finite linearly ordered vertex type, there is a connected graph with a crossing-free drawing whose edge count reaches 3n−6 for n≥3 and n−1 for n≤2. For n≥3, construct it inductively from a triangle by inserting each new vertex inside a triangular face and joining it to that face's three vertices; handle the smaller cases directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_connected_triangulated_planar_graph__p2m_5897f64b_d93f_46d0_b145_4fa00606e1c1_a3
    (V : Type) [Fintype V] [LinearOrder V] :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected ∧
      (3 ≤ Fintype.card V →
        3 * Fintype.card V - 6 ≤ H.edgeSet.ncard) ∧
      (Fintype.card V ≤ 2 →
        Fintype.card V - 1 ≤ H.edgeSet.ncard) := by
  sorry

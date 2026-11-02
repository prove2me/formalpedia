-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_bound__p2m_c26a86c1_c11b_4f85_a158_b9e12bec4015_a1
-- name    : WilliamsonShmoys.planar_completion_edge_bound__p2m_c26a86c1_c11b_4f85_a158_b9e12bec4015_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:45:09.018199+00:00
-- url     : https://prove2.me/theorems/b62a415b-0d40-4987-91cd-cfcca09e56a9
-- title:
--   Complete a drawable connected graph to a triangulated planar supergraph
-- statement:
--   Every finite connected graph on at least three linearly ordered vertices with a crossing-free drawing has a drawable supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six; the original graph’s edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_edge_bound__p2m_c26a86c1_c11b_4f85_a158_b9e12bec4015_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) (hcard : 3 <= Fintype.card V) :
    ∃ (H : SimpleGraph V) (hdec : DecidableRel H.Adj),
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeFinset.card ≤ H.edgeFinset.card ∧
      H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry

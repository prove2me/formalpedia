-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_1667285d_a971_405b_b6c6_0157cfd0f6b9_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_1667285d_a971_405b_b6c6_0157cfd0f6b9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:28:25.650752+00:00
-- url     : https://prove2.me/theorems/a641d14b-2083-49f9-8715-0f20d0b3e1ec
-- title:
--   Edge bound for a maximal planar graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_1667285d_a971_405b_b6c6_0157cfd0f6b9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → H ≤ L → L = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry

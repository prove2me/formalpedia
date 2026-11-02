-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_edge_card_ge__p2m_1667285d_a971_405b_b6c6_0157cfd0f6b9_a1
-- name    : WilliamsonShmoys.planar_maximal_extension_edge_card_ge__p2m_1667285d_a971_405b_b6c6_0157cfd0f6b9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:28:22.697876+00:00
-- url     : https://prove2.me/theorems/8bdcd24b-0a33-4788-8eda-5b06fcc2996a
-- title:
--   Maximal planar extension without decreasing edge count
-- statement:
--   A connected drawable simple graph on at least three vertices has a maximal drawable simple supergraph on the same vertices, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_maximal_extension_edge_card_ge__p2m_1667285d_a971_405b_b6c6_0157cfd0f6b9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L → K ≤ L → L = K) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel K.Adj := Classical.decRel K.Adj
       H.edgeFinset.card ≤ K.edgeFinset.card) := by sorry

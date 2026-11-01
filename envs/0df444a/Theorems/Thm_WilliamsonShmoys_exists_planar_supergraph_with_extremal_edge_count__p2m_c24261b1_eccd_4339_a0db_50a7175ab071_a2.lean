-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_extremal_edge_count__p2m_c24261b1_eccd_4339_a0db_50a7175ab071_a2
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_extremal_edge_count__p2m_c24261b1_eccd_4339_a0db_50a7175ab071_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:20:22.26183+00:00
-- url     : https://prove2.me/theorems/99da7898-0d3e-41e3-bad9-9b286d32e26c
-- title:
--   Extend a planar drawing to a maximal planar graph
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertex set whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_with_extremal_edge_count__p2m_c24261b1_eccd_4339_a0db_50a7175ab071_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
        H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry

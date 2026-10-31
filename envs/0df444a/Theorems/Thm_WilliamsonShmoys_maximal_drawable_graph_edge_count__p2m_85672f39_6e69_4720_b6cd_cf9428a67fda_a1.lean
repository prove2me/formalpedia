-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_85672f39_6e69_4720_b6cd_cf9428a67fda_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_85672f39_6e69_4720_b6cd_cf9428a67fda_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:23:43.58349+00:00
-- url     : https://prove2.me/theorems/70a6424f-4889-4ef2-870f-ee6e7e607f96
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_85672f39_6e69_4720_b6cd_cf9428a67fda_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

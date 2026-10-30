-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_219a8e3b_c7d8_43b3_9ee1_a4b3ebf8e3f2_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_219a8e3b_c7d8_43b3_9ee1_a4b3ebf8e3f2_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:17:51.810644+00:00
-- url     : https://prove2.me/theorems/5e572803-fbe6-434b-828d-4b1eaacca01f
-- title:
--   An inclusion-maximal drawable graph has the triangulation edge count
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing and at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_219a8e3b_c7d8_43b3_9ee1_a4b3ebf8e3f2_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

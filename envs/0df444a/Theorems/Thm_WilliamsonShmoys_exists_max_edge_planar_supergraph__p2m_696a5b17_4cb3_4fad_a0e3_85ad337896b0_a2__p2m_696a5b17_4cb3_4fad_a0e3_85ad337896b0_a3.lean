-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_edge_planar_supergraph__p2m_696a5b17_4cb3_4fad_a0e3_85ad337896b0_a2__p2m_696a5b17_4cb3_4fad_a0e3_85ad337896b0_a3
-- name    : WilliamsonShmoys.exists_max_edge_planar_supergraph__p2m_696a5b17_4cb3_4fad_a0e3_85ad337896b0_a2__p2m_696a5b17_4cb3_4fad_a0e3_85ad337896b0_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:06:39.306411+00:00
-- url     : https://prove2.me/theorems/57a5d2a0-6002-4d73-ad7c-0d5b1a326044
-- title:
--   Existence of a maximum-edge drawn supergraph
-- statement:
--   Every finite graph with a planar drawing has a drawn supergraph whose edge count is at least the edge count of every drawn supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_max_edge_planar_supergraph__p2m_696a5b17_4cb3_4fad_a0e3_85ad337896b0_a2__p2m_696a5b17_4cb3_4fad_a0e3_85ad337896b0_a3 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, H.edgeSet ⊆ L.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry

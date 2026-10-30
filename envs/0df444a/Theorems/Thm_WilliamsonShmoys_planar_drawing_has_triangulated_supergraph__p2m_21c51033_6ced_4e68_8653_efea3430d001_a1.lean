-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph__p2m_21c51033_6ced_4e68_8653_efea3430d001_a1
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_21c51033_6ced_4e68_8653_efea3430d001_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:28:49.23807+00:00
-- url     : https://prove2.me/theorems/80e34e39-9312-4353-9ec3-c3ff17c125fa
-- title:
--   Extend a planar drawing to a maximal planar graph
-- statement:
--   For every finite simple graph on at least three ordered vertices with the supplied crossing-free drawing, there is a supergraph on the same vertices whose edge set contains the original edges and whose edge count is exactly three times the number of vertices minus six. A classical proof extracts a plane embedding, adds noncrossing edges until the graph is maximal planar, and applies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_21c51033_6ced_4e68_8653_efea3430d001_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

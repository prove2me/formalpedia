-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_4b84dc63_4552_46b2_9c09_25aab1a1759e_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_4b84dc63_4552_46b2_9c09_25aab1a1759e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:38:05.385747+00:00
-- url     : https://prove2.me/theorems/696a5b17-4cb3-4fad-a0e3-85ad337896b0
-- title:
--   Extend a finite planar drawing to an edge-maximal supergraph
-- statement:
--   Every finite graph with a planar drawing has a drawn supergraph on the same vertex type that is maximal under edge inclusion and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_4b84dc63_4552_46b2_9c09_25aab1a1759e_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧ ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet = K.edgeSet := by sorry

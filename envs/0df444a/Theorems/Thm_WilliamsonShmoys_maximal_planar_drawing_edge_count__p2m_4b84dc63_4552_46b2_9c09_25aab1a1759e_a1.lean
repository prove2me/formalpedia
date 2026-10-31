-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_4b84dc63_4552_46b2_9c09_25aab1a1759e_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4b84dc63_4552_46b2_9c09_25aab1a1759e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:37:54.310815+00:00
-- url     : https://prove2.me/theorems/46c214d7-d1a4-4ee3-932f-e6097b55f369
-- title:
--   Count the edges of a maximal finite planar drawing
-- statement:
--   A finite simple graph on at least three vertices whose planar drawing cannot be extended to a strictly larger drawn graph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4b84dc63_4552_46b2_9c09_25aab1a1759e_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hMax : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet = K.edgeSet) : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

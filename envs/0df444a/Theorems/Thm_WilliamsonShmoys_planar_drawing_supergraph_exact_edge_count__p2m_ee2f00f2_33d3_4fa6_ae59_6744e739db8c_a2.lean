-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_exact_edge_count__p2m_ee2f00f2_33d3_4fa6_ae59_6744e739db8c_a2
-- name    : WilliamsonShmoys.planar_drawing_supergraph_exact_edge_count__p2m_ee2f00f2_33d3_4fa6_ae59_6744e739db8c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:02:34.330736+00:00
-- url     : https://prove2.me/theorems/f3f359af-2762-432f-8e05-8cdbcb14d938
-- title:
--   Exact edge-count planar completion on the same vertices
-- statement:
--   Any drawable finite simple graph on at least three vertices can be extended, on the same vertex set, to a drawable simple graph with exactly three times the number of vertices minus six edges; the original edge set is included in the completion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_supergraph_exact_edge_count__p2m_ee2f00f2_33d3_4fa6_ae59_6744e739db8c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry

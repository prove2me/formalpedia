-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_898ed614_bb9e_4a02_a507_ff39f26b30a9_a1
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_898ed614_bb9e_4a02_a507_ff39f26b30a9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:20:08.99598+00:00
-- url     : https://prove2.me/theorems/a9e1a1a2-842d-40ac-8796-98757b50fe5c
-- title:
--   Complete a planar drawing to a triangulation with the maximal edge count
-- statement:
--   Any finite drawable simple graph with at least three vertices is contained, on the same vertex set, in a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_898ed614_bb9e_4a02_a507_ff39f26b30a9_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ HasPlanarDrawingOn K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

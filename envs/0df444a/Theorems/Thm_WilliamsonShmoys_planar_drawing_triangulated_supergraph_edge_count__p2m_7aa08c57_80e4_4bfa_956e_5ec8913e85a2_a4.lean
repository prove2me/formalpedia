-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph_edge_count__p2m_7aa08c57_80e4_4bfa_956e_5ec8913e85a2_a4
-- name    : WilliamsonShmoys.planar_drawing_triangulated_supergraph_edge_count__p2m_7aa08c57_80e4_4bfa_956e_5ec8913e85a2_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:27:22.659734+00:00
-- url     : https://prove2.me/theorems/878ddd3e-03fb-448c-a8d8-103ff049e818
-- title:
--   Triangulated supergraph edge count for a planar drawing
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly 3|V|−6, with at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulated_supergraph_edge_count__p2m_7aa08c57_80e4_4bfa_956e_5ec8913e85a2_a4 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

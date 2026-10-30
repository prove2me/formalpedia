-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_edge_count__p2m_f6fbb2eb_cab6_4ebc_b0c8_9e00fa476533_a2
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count__p2m_f6fbb2eb_cab6_4ebc_b0c8_9e00fa476533_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T21:23:48.015608+00:00
-- url     : https://prove2.me/theorems/b4ae0234-df79-4465-81f3-c37b6c00cb9e
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite linearly ordered vertex type with at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count__p2m_f6fbb2eb_cab6_4ebc_b0c8_9e00fa476533_a2 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) : M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

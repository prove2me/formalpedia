-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_exact_edge_count__p2m_fc475467_cefd_44fd_810b_5d1d49565f31_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_exact_edge_count__p2m_fc475467_cefd_44fd_810b_5d1d49565f31_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:52:24.292304+00:00
-- url     : https://prove2.me/theorems/cc47608f-2603-41cf-ab7f-de8b10963069
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly 3|V| − 6 edges. The independent proof route is to show maximality makes the drawing a triangulation, then apply Euler’s formula and count edge-face incidences, with hV handling the natural subtraction boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_exact_edge_count__p2m_fc475467_cefd_44fd_810b_5d1d49565f31_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : 3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry

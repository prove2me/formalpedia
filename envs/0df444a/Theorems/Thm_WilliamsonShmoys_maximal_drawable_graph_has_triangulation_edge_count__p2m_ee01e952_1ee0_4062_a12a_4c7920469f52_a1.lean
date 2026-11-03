-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_edge_count__p2m_ee01e952_1ee0_4062_a12a_4c7920469f52_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count__p2m_ee01e952_1ee0_4062_a12a_4c7920469f52_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:26:30.056669+00:00
-- url     : https://prove2.me/theorems/afa4574a-1607-44bb-93bd-58940dcb1487
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on those vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count__p2m_ee01e952_1ee0_4062_a12a_4c7920469f52_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj] (hcard : 3 ≤ Fintype.card V) (hM : HasPlanarDrawingOn M) (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) : 3 * Fintype.card V = M.edgeFinset.card + 6 := by sorry

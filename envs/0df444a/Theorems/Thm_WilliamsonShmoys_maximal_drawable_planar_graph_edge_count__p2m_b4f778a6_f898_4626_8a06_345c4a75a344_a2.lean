-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_graph_edge_count__p2m_b4f778a6_f898_4626_8a06_345c4a75a344_a2
-- name    : WilliamsonShmoys.maximal_drawable_planar_graph_edge_count__p2m_b4f778a6_f898_4626_8a06_345c4a75a344_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:46:49.603132+00:00
-- url     : https://prove2.me/theorems/67af1d40-5710-49f6-8447-77c85edb00fd
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_planar_graph_edge_count__p2m_b4f778a6_f898_4626_8a06_345c4a75a344_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry

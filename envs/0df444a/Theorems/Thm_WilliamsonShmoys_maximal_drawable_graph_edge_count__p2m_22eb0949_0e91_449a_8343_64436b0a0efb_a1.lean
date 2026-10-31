-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:59:38.230295+00:00
-- url     : https://prove2.me/theorems/76a86dc1-411a-4f86-8755-ab6ac02ce22d
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite vertices that has no drawable strict supergraph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) : 3 * Fintype.card V - 6 = T.edgeSet.ncard := by sorry

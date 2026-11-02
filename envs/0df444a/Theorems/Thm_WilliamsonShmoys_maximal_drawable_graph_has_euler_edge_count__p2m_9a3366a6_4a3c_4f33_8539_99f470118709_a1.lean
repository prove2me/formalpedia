-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count__p2m_9a3366a6_4a3c_4f33_8539_99f470118709_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_9a3366a6_4a3c_4f33_8539_99f470118709_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:52:17.729672+00:00
-- url     : https://prove2.me/theorems/7cf72e3d-7b9d-4e33-bfe4-614d5c224b98
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_9a3366a6_4a3c_4f33_8539_99f470118709_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (dM : DecidableRel M.Adj) (hM : HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) (hmax : ∀ (N : SimpleGraph V) (dN : DecidableRel N.Adj), M <= N → HasPlanarDrawingOn N → N = M) : M.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry

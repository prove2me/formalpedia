-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulated_edge_count__p2m_637d8540_4fa2_4bdf_8eaf_997caf9c33c1_a2
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_triangulated_edge_count__p2m_637d8540_4fa2_4bdf_8eaf_997caf9c33c1_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:52:49.280503+00:00
-- url     : https://prove2.me/theorems/4b104b32-56a0-4b02-b537-5e9d1339dc2d
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_has_triangulated_edge_count__p2m_637d8540_4fa2_4bdf_8eaf_997caf9c33c1_a2 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) [DecidableRel P.Adj] (hcard : 3 ≤ Fintype.card V) (hP : HasPlanarDrawingOn P) (hmax : ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q = P) : P.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry

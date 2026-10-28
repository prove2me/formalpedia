-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_from_arcs_6a5dd28f
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_from_arcs_6a5dd28f
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T21:44:33.096186+00:00
-- url     : https://prove2.me/theorems/91a5eb3c-94d5-45a2-9656-0ab8aa1aa564
-- title:
--   A maximal graph for the continuous-arc drawing predicate has the planar maximum edge count
-- statement:
--   An inclusion-maximal graph with a crossing-free continuous-arc drawing on a finite linearly ordered vertex type with at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_from_arcs_6a5dd28f {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 <= Fintype.card V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hmax : forall N : SimpleGraph V, M <= N -> WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

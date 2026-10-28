-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_v2
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T23:23:49.07413+00:00
-- url     : https://prove2.me/theorems/a8911ec3-54fa-4606-98af-4e2f9062f162
-- title:
--   Exact edge count for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly $3|V|-6$ edges. The proof must formalize the planar triangulation and Euler-count argument for the attached continuous-arc drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_v2 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hV : 3 <= Fintype.card V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N) (hmax : ∀ K : SimpleGraph V, N <= K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) : 3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry

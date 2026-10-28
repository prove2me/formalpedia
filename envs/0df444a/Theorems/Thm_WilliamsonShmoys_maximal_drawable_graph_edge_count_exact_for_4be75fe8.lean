-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_exact_for_4be75fe8
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_exact_for_4be75fe8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:43:54.886353+00:00
-- url     : https://prove2.me/theorems/7721b27c-f110-41cf-87bd-6f874bcfc3d8
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_exact_for_4be75fe8
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ H : SimpleGraph V, M ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

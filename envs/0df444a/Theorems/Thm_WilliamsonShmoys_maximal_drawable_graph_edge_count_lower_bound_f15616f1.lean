-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound_f15616f1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_f15616f1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:15:29.630038+00:00
-- url     : https://prove2.me/theorems/90faeda0-6a0b-45c2-a8be-17d7a1bd82be
-- title:
--   Lower edge bound for a maximal drawable graph
-- statement:
--   A graph maximal under drawable edge extensions on at least three vertices has at least 3n − 6 edges. This includes n = 3, where maximality forces the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_f15616f1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ J : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn J →
      H ≤ J → H = J) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry

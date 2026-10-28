-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_exact_edge_count_for_f2fc27dd
-- name    : WilliamsonShmoys.maximal_planar_completion_exact_edge_count_for_f2fc27dd
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:54:01.531111+00:00
-- url     : https://prove2.me/theorems/c3fbd97c-1077-40ea-9553-45bcba514778
-- title:
--   Extend a drawable graph to the triangulation edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. For three vertices, the completion is the triangle; for larger sets, a proof can augment the drawing to a triangulation and count its faces using Euler’s formula. This removes the topological completion and edge-count argument from the parent. It preserves the exact vertex-count allowance and count. The remaining core obligation is to formalize that completion for the given arc-based drawing predicate, including disconnected drawings.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_completion_exact_edge_count_for_f2fc27dd
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

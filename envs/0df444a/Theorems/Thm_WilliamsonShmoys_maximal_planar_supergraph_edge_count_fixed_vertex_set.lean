-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_fixed_vertex_set
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count_fixed_vertex_set
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:47:33.892378+00:00
-- url     : https://prove2.me/theorems/8988d4b7-1148-4c6d-a075-6122aca6f987
-- title:
--   Edge count of a maximal planar graph on a fixed vertex set
-- statement:
--   A maximal planar graph on a finite fixed vertex set of size at least three has exactly 3|V| − 6 edges. This removes the topological and Euler-counting work from the parent. An independent proof route is to show that maximality makes the embedding a triangulation, handle the three-vertex case as K₃, and for larger vertex sets count triangular face-edge incidences together with Euler’s formula. The lower bound is retained because the formula does not hold for smaller maximal planar graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count_fixed_vertex_set
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ H : SimpleGraph V,
      M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

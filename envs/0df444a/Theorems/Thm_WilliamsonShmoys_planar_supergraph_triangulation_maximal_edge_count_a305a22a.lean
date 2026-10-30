-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_maximal_edge_count_a305a22a
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_maximal_edge_count_a305a22a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:31:40.728477+00:00
-- url     : https://prove2.me/theorems/cdf61d08-37b6-4d1c-b1c7-3220d3dc4aed
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertices has exactly 3|V|−6 edges. This isolates the topological maximal-planar and Euler-counting argument required by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation_maximal_edge_count_a305a22a
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry

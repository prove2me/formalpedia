-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_707fd91e
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_707fd91e
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:37:54.464336+00:00
-- url     : https://prove2.me/theorems/93cad1d3-6631-4871-91db-d5199271705a
-- title:
--   Maximal drawable graphs meet the planar edge bound
-- statement:
--   An inclusion-maximal drawable simple graph on a fixed finite vertex set of size at least three has at least 3|V| - 6 edges. Maximality excludes disconnected components and nontriangular faces; the three-vertex case forces the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_707fd91e
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry

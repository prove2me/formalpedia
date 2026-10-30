-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_a305a22a
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_a305a22a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:41:13.484986+00:00
-- url     : https://prove2.me/theorems/36aa6325-b287-4fba-8340-d6a985165771
-- title:
--   Lower edge bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has at least 3|V| - 6 edges. This removes the maximality-to-triangulation and lower-counting obligation from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_a305a22a
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry

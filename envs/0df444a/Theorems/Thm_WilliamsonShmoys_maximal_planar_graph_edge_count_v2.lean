-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_v2
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:15:13.672951+00:00
-- url     : https://prove2.me/theorems/7b666f1f-cdb7-4d90-9427-78a3a6e0c53f
-- title:
--   Edge lower bound for an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least `3|V| - 6` edges. The argument uses maximality to obtain triangular faces, then Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R →
      Set.Subset Q.edgeSet R.edgeSet →
      R.edgeSet = Q.edgeSet) :
    3 * Fintype.card V ≤ Q.edgeSet.ncard + 6 := by sorry

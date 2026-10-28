-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_full_edge_supergraph_maximal_edge_count_20261028
-- name    : WilliamsonShmoys.planar_full_edge_supergraph_maximal_edge_count_20261028
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:27:55.00792+00:00
-- url     : https://prove2.me/theorems/3b87e36d-2935-42f0-8968-a4d7c71c3d13
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A maximal planar simple graph on a finite ordered vertex type with at least three vertices has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_full_edge_supergraph_maximal_edge_count_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

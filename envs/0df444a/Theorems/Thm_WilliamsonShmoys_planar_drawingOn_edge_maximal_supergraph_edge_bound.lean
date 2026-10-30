-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_maximal_supergraph_edge_bound
-- name    : WilliamsonShmoys.planar_drawingOn_edge_maximal_supergraph_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:53:54.402946+00:00
-- url     : https://prove2.me/theorems/e5a7f9d6-bace-4e4e-8552-536c6d6539c9
-- title:
--   Edge bound for an edge-maximal planar graph
-- statement:
--   An edge-maximal graph with a planar drawing on a finite ordered vertex type of size at least three has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_edge_maximal_supergraph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → K ≤ L → L ≤ K) :
    3 * (Fintype.card V : Int) - 6 <= (K.edgeSet.ncard : Int) := by sorry

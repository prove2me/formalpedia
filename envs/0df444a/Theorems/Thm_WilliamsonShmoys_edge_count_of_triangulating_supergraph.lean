-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_triangulating_supergraph
-- name    : WilliamsonShmoys.edge_count_of_triangulating_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:00:25.326+00:00
-- url     : https://prove2.me/theorems/d0fbf8a5-dc2f-49cb-98ec-1250fd244082
-- title:
--   Edge count of a maximal planar supergraph
-- statement:
--   An inclusion-maximal planar supergraph of a connected graph with at least three vertices has the maximal planar edge count. This child removes the planar-topological counting argument from the parent. Prove it by showing maximality forces triangular faces, then combine face-edge incidence counting with Euler’s formula. The hypotheses preserve connectedness in K and exclude the small-vertex exceptions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_triangulating_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (J K : SimpleGraph V)
    (hJK : J.edgeSet ⊆ K.edgeSet)
    (hConn : J.Connected)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry

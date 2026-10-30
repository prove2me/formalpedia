-- Prove2me | Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_has_extremal_edge_count
-- name    : WilliamsonShmoys.inclusion_maximal_planar_has_extremal_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:43:36.407387+00:00
-- url     : https://prove2.me/theorems/2cb1de58-9250-4fe4-a5b9-435246c2a8e6
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal graph with the specified planar drawing on at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.inclusion_maximal_planar_has_extremal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

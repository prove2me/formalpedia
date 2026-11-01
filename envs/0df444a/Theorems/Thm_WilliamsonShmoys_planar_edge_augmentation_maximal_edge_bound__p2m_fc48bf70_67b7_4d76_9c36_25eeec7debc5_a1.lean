-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_maximal_edge_bound__p2m_fc48bf70_67b7_4d76_9c36_25eeec7debc5_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation_maximal_edge_bound__p2m_fc48bf70_67b7_4d76_9c36_25eeec7debc5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:37:29.277655+00:00
-- url     : https://prove2.me/theorems/66b1df0d-2f5a-4a83-9f88-9b13f7439798
-- title:
--   Euler bound for maximal drawable graphs
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has at least 3|V|−6 edges, by the planar Euler bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.planar_edge_augmentation_maximal_edge_bound__p2m_fc48bf70_67b7_4d76_9c36_25eeec7debc5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry

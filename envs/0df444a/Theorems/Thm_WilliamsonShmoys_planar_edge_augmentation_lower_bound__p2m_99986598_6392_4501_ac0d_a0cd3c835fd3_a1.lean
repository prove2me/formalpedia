-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_lower_bound__p2m_99986598_6392_4501_ac0d_a0cd3c835fd3_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation_lower_bound__p2m_99986598_6392_4501_ac0d_a0cd3c835fd3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:11:37.475654+00:00
-- url     : https://prove2.me/theorems/5e34af62-bc93-4e27-8f77-f0a9265acaf1
-- title:
--   Planar graphs admit an edge-rich drawable supergraph
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type with at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_lower_bound__p2m_99986598_6392_4501_ac0d_a0cd3c835fd3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V, L ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry

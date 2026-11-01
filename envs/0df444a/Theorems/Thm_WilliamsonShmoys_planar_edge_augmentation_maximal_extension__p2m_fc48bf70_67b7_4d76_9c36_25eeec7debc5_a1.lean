-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_maximal_extension__p2m_fc48bf70_67b7_4d76_9c36_25eeec7debc5_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation_maximal_extension__p2m_fc48bf70_67b7_4d76_9c36_25eeec7debc5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:37:26.569196+00:00
-- url     : https://prove2.me/theorems/1299aa4d-98c0-4add-b63d-d780039a027b
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal among drawable supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.planar_edge_augmentation_maximal_extension__p2m_fc48bf70_67b7_4d76_9c36_25eeec7debc5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M →
          WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry

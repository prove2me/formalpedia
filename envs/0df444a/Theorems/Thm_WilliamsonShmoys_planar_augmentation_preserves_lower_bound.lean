-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_preserves_lower_bound
-- name    : WilliamsonShmoys.planar_augmentation_preserves_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:50:00.737057+00:00
-- url     : https://prove2.me/theorems/61ae66c6-986d-4f07-8042-2c1fde16d2b8
-- title:
--   A drawable graph has a drawable supergraph meeting the planar edge bound
-- statement:
--   Any drawable simple graph on at least three finite ordered vertices has a drawable supergraph on the same vertices with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_augmentation_preserves_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V <= L.edgeSet.ncard + 6 := by sorry

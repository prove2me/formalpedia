-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_augmentation_for_edge_bound__p2m_1016eb9f_955e_4666_8793_89a9a11ff9b9_a5
-- name    : WilliamsonShmoys.planar_drawing_maximal_augmentation_for_edge_bound__p2m_1016eb9f_955e_4666_8793_89a9a11ff9b9_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T01:52:06.229835+00:00
-- url     : https://prove2.me/theorems/1a05aeae-3861-45b6-82f2-f3b3496c6f75
-- title:
--   Extend a planar drawing to a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_augmentation_for_edge_bound__p2m_1016eb9f_955e_4666_8793_89a9a11ff9b9_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L <= M →
          WilliamsonShmoys.HasPlanarDrawingOn M → M <= L := by sorry

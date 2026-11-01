-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_augmentation__p2m_be074bdb_79a8_40c0_b245_62762170066e_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal_augmentation__p2m_be074bdb_79a8_40c0_b245_62762170066e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:31:54.475973+00:00
-- url     : https://prove2.me/theorems/867a30c3-e0cd-4780-a6e7-8570584f57fd
-- title:
--   Maximal planar supergraph augmentation
-- statement:
--   Every drawable finite graph on at least three vertices has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_augmentation__p2m_be074bdb_79a8_40c0_b245_62762170066e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L →
          WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry

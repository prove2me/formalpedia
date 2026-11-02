-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_maximal_extension__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2
-- name    : WilliamsonShmoys.planar_drawing_augmentation_maximal_extension__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:27:39.380952+00:00
-- url     : https://prove2.me/theorems/951d4718-f29f-424f-97bb-a9fab7a690a6
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Any drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertex set. This is a finite choice argument: maximize the number of edges among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_augmentation_maximal_extension__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L := by sorry

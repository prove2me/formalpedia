-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_a4df0fa7_688f_4bd0_bfe4_ea6603f7e8eb_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_a4df0fa7_688f_4bd0_bfe4_ea6603f7e8eb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:46:32.34655+00:00
-- url     : https://prove2.me/theorems/fe6641dc-c570-459f-b36e-e7aed3590a75
-- title:
--   Extend a planar drawing to a maximal planar graph
-- statement:
--   Any finite graph with a drawing as specified can be extended, on the same vertex type, to a drawn graph whose edge set is maximal among drawn supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension__p2m_a4df0fa7_688f_4bd0_bfe4_ea6603f7e8eb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ P : SimpleGraph V,
      K.edgeSet ⊆ P.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ L : SimpleGraph V,
        P.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet ⊆ P.edgeSet := by sorry

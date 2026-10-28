-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists__p2m_6aa45121_eedc_4241_b18d_7cc974f0060a_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_6aa45121_eedc_4241_b18d_7cc974f0060a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:35:30.797996+00:00
-- url     : https://prove2.me/theorems/30ea4785-5bd8-46ba-aa70-67a6b8ccdea6
-- title:
--   Every finite drawable graph has a maximal drawable extension
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in an inclusion-maximal drawable graph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_6aa45121_eedc_4241_b18d_7cc974f0060a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ K : SimpleGraph V,
        M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = M := by sorry

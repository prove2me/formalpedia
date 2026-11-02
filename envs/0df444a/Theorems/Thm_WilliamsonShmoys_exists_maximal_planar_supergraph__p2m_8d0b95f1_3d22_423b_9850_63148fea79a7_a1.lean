-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_8d0b95f1_3d22_423b_9850_63148fea79a7_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8d0b95f1_3d22_423b_9850_63148fea79a7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:24:16.350653+00:00
-- url     : https://prove2.me/theorems/4a6cafb2-5187-4c05-9bfd-093765f16903
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has an inclusion-maximal drawable supergraph on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8d0b95f1_3d22_423b_9850_63148fea79a7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKDrawing : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by sorry

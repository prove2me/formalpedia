-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_4d475df2_1a8a_43aa_9ce4_014b937605e8_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4d475df2_1a8a_43aa_9ce4_014b937605e8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:32:03.948299+00:00
-- url     : https://prove2.me/theorems/d52a840c-ba5a-4e95-ae45-e4d9339ec21f
-- title:
--   Existence of a maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4d475df2_1a8a_43aa_9ce4_014b937605e8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G ≤ H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by sorry

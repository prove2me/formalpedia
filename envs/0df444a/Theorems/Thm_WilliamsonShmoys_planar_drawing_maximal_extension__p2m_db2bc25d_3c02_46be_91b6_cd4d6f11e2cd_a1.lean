-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_db2bc25d_3c02_46be_91b6_cd4d6f11e2cd_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_db2bc25d_3c02_46be_91b6_cd4d6f11e2cd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:52:32.395817+00:00
-- url     : https://prove2.me/theorems/3e187282-ed42-4b71-bc6a-a0a726731916
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under inclusion among drawable supergraphs. The statement also applies when the vertex count is exactly three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_db2bc25d_3c02_46be_91b6_cd4d6f11e2cd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ R : SimpleGraph V, G ≤ R ∧ HasPlanarDrawingOn R ∧
      ∀ H : SimpleGraph V, R ≤ H → HasPlanarDrawingOn H → H = R := by sorry

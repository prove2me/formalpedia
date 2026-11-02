-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a2
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:12:55.464832+00:00
-- url     : https://prove2.me/theorems/4a79f535-7c3f-422a-88d6-6cd015f3e78e
-- title:
--   Finite maximal planar extension
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph that is maximal under adding edges on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hP : HasPlanarDrawingOn P) :
    ∃ H : SimpleGraph V,
      P ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) := by sorry

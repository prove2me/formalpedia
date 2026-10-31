-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_extension__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:04:32.839093+00:00
-- url     : https://prove2.me/theorems/9376816e-eb5e-481a-8240-6f36f24b215f
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph maximal under inclusion among drawable graphs on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_extension__p2m_3e96e4b7_ffaf_421c_b46f_8949f4d2645c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H := by sorry

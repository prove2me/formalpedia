-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1
-- name    : WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:36:14.054408+00:00
-- url     : https://prove2.me/theorems/1637ad82-25e4-48bc-a54a-763615ae1028
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K ≤ H := by sorry

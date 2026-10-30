-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_87706138_1b1b_4896_af61_3aff6d2d47f5_a1
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_87706138_1b1b_4896_af61_3aff6d2d47f5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:20:41.340298+00:00
-- url     : https://prove2.me/theorems/d772272e-afb6-4b86-be52-b7723ab16c69
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph that has no strictly larger drawable supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_87706138_1b1b_4896_af61_3aff6d2d47f5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V, K ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by sorry

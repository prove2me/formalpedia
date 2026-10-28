-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion_a3bf2761_3b00_45d2_af0e_a4c0f6d1919f
-- name    : WilliamsonShmoys.exists_maximal_planar_completion_a3bf2761_3b00_45d2_af0e_a4c0f6d1919f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:41:24.890246+00:00
-- url     : https://prove2.me/theorems/e231578e-7c6e-45d2-b80e-13db1c65d4e6
-- title:
--   Every drawable finite graph has a maximal drawable completion
-- statement:
--   Every finite graph with a planar drawing is contained in a drawable graph that is maximal among drawable supergraphs on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_completion_a3bf2761_3b00_45d2_af0e_a4c0f6d1919f
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry

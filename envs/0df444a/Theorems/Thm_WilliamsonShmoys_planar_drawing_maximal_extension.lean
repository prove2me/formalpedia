-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:48:32.425233+00:00
-- url     : https://prove2.me/theorems/ee12e918-a26e-448c-8ea8-603e90402fe1
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable graph on at least three vertices is contained in a drawable graph on the same vertices that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry

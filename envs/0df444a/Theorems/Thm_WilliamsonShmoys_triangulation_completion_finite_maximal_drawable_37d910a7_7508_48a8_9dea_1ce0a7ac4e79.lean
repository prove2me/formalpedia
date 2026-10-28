-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_completion_finite_maximal_drawable_37d910a7_7508_48a8_9dea_1ce0a7ac4e79
-- name    : WilliamsonShmoys.triangulation_completion_finite_maximal_drawable_37d910a7_7508_48a8_9dea_1ce0a7ac4e79
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:38:30.845714+00:00
-- url     : https://prove2.me/theorems/2639cd7e-51d2-4024-9a0a-1ba4e6e9f920
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph maximal among drawable supergraphs on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_completion_finite_maximal_drawable_37d910a7_7508_48a8_9dea_1ce0a7ac4e79
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      (∀ R : SimpleGraph V, Q ≤ R →
        WilliamsonShmoys.HasPlanarDrawingOn R → R = Q) := by sorry

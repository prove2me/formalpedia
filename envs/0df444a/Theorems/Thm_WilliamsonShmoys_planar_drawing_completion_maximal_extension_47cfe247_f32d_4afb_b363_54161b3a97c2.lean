-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_maximal_extension_47cfe247_f32d_4afb_b363_54161b3a97c2
-- name    : WilliamsonShmoys.planar_drawing_completion_maximal_extension_47cfe247_f32d_4afb_b363_54161b3a97c2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:54:59.751754+00:00
-- url     : https://prove2.me/theorems/a3c22528-dda6-4e4a-b9ba-8cbe7053c160
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph maximal under inclusion among drawable graphs on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_completion_maximal_extension_47cfe247_f32d_4afb_b363_54161b3a97c2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P →
        WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by sorry

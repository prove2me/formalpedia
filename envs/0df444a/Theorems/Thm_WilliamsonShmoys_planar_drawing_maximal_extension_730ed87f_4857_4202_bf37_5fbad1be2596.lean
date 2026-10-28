-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_730ed87f_4857_4202_bf37_5fbad1be2596
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_730ed87f_4857_4202_bf37_5fbad1be2596
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:49:31.557907+00:00
-- url     : https://prove2.me/theorems/f80766ef-d994-4baa-ba7e-771d810ec18a
-- title:
--   Every finite planar drawing has a maximal drawable completion
-- statement:
--   Every drawable simple graph on a finite ordered vertex type is contained in a drawable supergraph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_maximal_extension_730ed87f_4857_4202_bf37_5fbad1be2596 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) : ∃ T : SimpleGraph V, M ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by sorry

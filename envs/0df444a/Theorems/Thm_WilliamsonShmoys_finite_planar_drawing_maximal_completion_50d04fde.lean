-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_drawing_maximal_completion_50d04fde
-- name    : WilliamsonShmoys.finite_planar_drawing_maximal_completion_50d04fde
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:07:59.293677+00:00
-- url     : https://prove2.me/theorems/e681930e-be75-465a-88dd-e9421a4050fe
-- title:
--   Finite maximal drawable completion
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that has no strictly larger drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.finite_planar_drawing_maximal_completion_50d04fde {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by sorry

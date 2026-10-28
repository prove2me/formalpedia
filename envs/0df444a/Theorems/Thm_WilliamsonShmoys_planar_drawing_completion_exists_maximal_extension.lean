-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_exists_maximal_extension
-- name    : WilliamsonShmoys.planar_drawing_completion_exists_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:00:09.860971+00:00
-- url     : https://prove2.me/theorems/ab38813f-2d4d-4231-a091-366fa4441a97
-- title:
--   Existence of a maximal drawable extension for drawing completion
-- statement:
--   Every drawable simple graph on a finite ordered vertex type has a drawable supergraph maximal under drawable supergraph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_completion_exists_maximal_extension {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ (∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = K) := by sorry

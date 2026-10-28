-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_maximal_extension
-- name    : WilliamsonShmoys.planar_drawing_completion_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:46:28.711415+00:00
-- url     : https://prove2.me/theorems/aa4cbf4e-faf1-4c4c-80a2-bcd13e1c21a8
-- title:
--   Maximal drawable extension on a fixed vertex set
-- statement:
--   Every drawable finite simple graph on a fixed vertex type has a drawable supergraph on that same vertex type that is maximal under drawable supergraph inclusion. No minimum-size hypothesis is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_completion_maximal_extension {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry

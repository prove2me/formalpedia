-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_for_triangulation
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension_for_triangulation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:36:11.766961+00:00
-- url     : https://prove2.me/theorems/27d6bb42-fdd8-41f8-bed3-58cc890e2107
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every graph with a planar drawing on a finite vertex type has a drawable supergraph on the same vertices that contains every drawable supergraph of the input.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension_for_triangulation {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ J : SimpleGraph V, H ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧ ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_extension_9c238260_8e64_40d3_b87d_42af728950e9
-- name    : WilliamsonShmoys.planar_drawing_completion_extension_9c238260_8e64_40d3_b87d_42af728950e9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:33:37.196517+00:00
-- url     : https://prove2.me/theorems/30212c61-6f14-4369-98fb-dd3bd4dd346f
-- title:
--   Maximal drawable extension on the same vertex type
-- statement:
--   Every drawable simple graph on a finite ordered vertex type is contained in an inclusion-maximal drawable simple graph on the same vertex type, with at least as many edges. No lower bound on the number of vertices is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_completion_extension_9c238260_8e64_40d3_b87d_42af728950e9 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDrawing : HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H := by sorry

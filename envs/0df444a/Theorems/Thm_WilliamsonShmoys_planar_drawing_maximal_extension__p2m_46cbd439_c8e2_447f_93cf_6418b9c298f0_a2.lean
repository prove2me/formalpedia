-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_46cbd439_c8e2_447f_93cf_6418b9c298f0_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_46cbd439_c8e2_447f_93cf_6418b9c298f0_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:31:04.400518+00:00
-- url     : https://prove2.me/theorems/444b006d-e697-4eb5-bac6-c0d681524154
-- title:
--   Extend a planar drawing to an edge-maximal planar graph
-- statement:
--   Every finite graph with a crossing-free drawing on the given vertex type is contained in a planar graph on that same vertex type that has no strictly larger planar supergraph. The finite set of possible edges permits choosing a planar supergraph with the largest edge set; the drawing and vertex-count hypotheses are preserved.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_46cbd439_c8e2_447f_93cf_6418b9c298f0_a2 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hCard : 3 ≤ Fintype.card V) : ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ (∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) := by sorry

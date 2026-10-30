-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_for_triangulation
-- name    : WilliamsonShmoys.maximal_drawing_edge_count_for_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:36:48.919568+00:00
-- url     : https://prove2.me/theorems/ca1df20e-3099-402f-9ff2-a8aaf3760c01
-- title:
--   Edge count of an inclusion-maximal planar drawing
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly 3n−6 edges. The condition allows equality K = J and rules out every proper drawable extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_drawing_edge_count_for_triangulation {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J) : 3 * Fintype.card V = J.edgeSet.ncard + 6 := by sorry

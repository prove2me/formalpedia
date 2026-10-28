-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_maximal_edge_lower_bound
-- name    : WilliamsonShmoys.planar_drawing_completion_maximal_edge_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:03:40.481993+00:00
-- url     : https://prove2.me/theorems/6e2fdad8-9cdb-42c4-982b-a706cf4054f1
-- title:
--   Edge lower bound for maximal drawable graphs in drawing completion
-- statement:
--   A drawable graph on at least three vertices that is maximal under drawable supergraph inclusion has at least `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_completion_maximal_edge_lower_bound {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K) (hMax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = K) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry

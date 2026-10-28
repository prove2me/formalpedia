-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_for_edge_bound_v2
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_edge_bound_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:37:50.075556+00:00
-- url     : https://prove2.me/theorems/27de9307-8f74-43f6-a87c-59e7b05a3cec
-- title:
--   Extend a planar drawing to an edge-maximal planar supergraph
-- statement:
--   A finite simple graph with the stated crossing-free drawing and at least three vertices has an inclusion-maximal planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_edge_bound_v2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ K' : SimpleGraph V, K ≤ K' → WilliamsonShmoys.HasPlanarDrawingOn K' → K' = K := by sorry

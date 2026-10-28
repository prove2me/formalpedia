-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_can_be_augmented_to_edge_count
-- name    : WilliamsonShmoys.planar_graph_can_be_augmented_to_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:50:23.31596+00:00
-- url     : https://prove2.me/theorems/5956d2a1-afad-4c5c-bc6a-fee0d4abf9bd
-- title:
--   Planar graph augmentation to a triangulation
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex set of size at least three is a subgraph of a graph on that same vertex set that has a crossing-free drawing and exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_can_be_augmented_to_edge_count {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

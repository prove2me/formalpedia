-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_augmentation_for_euler_bound
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_augmentation_for_euler_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:20:55.508104+00:00
-- url     : https://prove2.me/theorems/52aeed95-458e-46e0-ad35-c5b4fde8ed3c
-- title:
--   Planar augmentation to an extremal supergraph
-- statement:
--   A finite simple graph on at least three vertices with a drawing satisfying `HasPlanarDrawingOn` is a subgraph of a graph on the same vertices with such a drawing and exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_augmentation_for_euler_bound {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_augmentation
-- name    : WilliamsonShmoys.planar_graph_triangulation_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:24:34.193585+00:00
-- url     : https://prove2.me/theorems/56e445a1-f328-4edf-b92e-b00522a98372
-- title:
--   Augment a planar drawing to a triangulation
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly 3|V| − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_triangulation_augmentation {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn U) (hV : 3 ≤ Fintype.card V) : ∃ W : SimpleGraph V, U ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧ 3 * Fintype.card V = W.edgeSet.ncard + 6 := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_edge_completion__p2m_1fea64f0_2aef_4373_b504_03974af27e28_a2
-- name    : WilliamsonShmoys.planarDrawing_edge_completion__p2m_1fea64f0_2aef_4373_b504_03974af27e28_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:12:34.732013+00:00
-- url     : https://prove2.me/theorems/a80fc761-9cba-4eba-813f-0d90fd63a821
-- title:
--   Completion of a planar drawing to a maximal planar graph
-- statement:
--   Any finite simple graph with at least three vertices that has a crossing-free drawing can be extended, on the same vertex set, to a crossing-free simple supergraph with exactly 3|V|−6 edges. This is the augmentation-to-triangulation step: connect components and add drawable edges until maximal, then use Euler’s formula. It removes the topological embedding and face-count work from the parent; that remains the core obligation in this child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_edge_completion__p2m_1fea64f0_2aef_4373_b504_03974af27e28_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 <= Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_augmentation__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:16:16.353438+00:00
-- url     : https://prove2.me/theorems/4bec975c-9ba0-4d47-8fe9-c081e6a8c028
-- title:
--   Add one edge below the planar bound
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than 3|V|−6 edges, one can add exactly one edge while keeping a drawing on the same vertex set. This removes the topological edge-insertion step from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_augmentation__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hEdges : H.edgeSet.ncard < 3 * Fintype.card V - 6) : ∃ K : SimpleGraph V, H ≤ K ∧ K.edgeSet.ncard = H.edgeSet.ncard + 1 ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry

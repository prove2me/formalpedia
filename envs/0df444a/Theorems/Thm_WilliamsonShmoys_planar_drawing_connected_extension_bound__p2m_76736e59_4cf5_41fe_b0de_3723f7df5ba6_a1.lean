-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_bound__p2m_76736e59_4cf5_41fe_b0de_3723f7df5ba6_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_bound__p2m_76736e59_4cf5_41fe_b0de_3723f7df5ba6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:09.006894+00:00
-- url     : https://prove2.me/theorems/d270c124-96c5-427a-8655-88aa20edeadc
-- title:
--   Connected planar extension preserves the edge count bound
-- statement:
--   A finite drawn graph on at least three vertices has a connected planar supergraph on the same vertex set, and the supergraph has at least as many edges. This isolates the component-joining step needed to reduce the target to the connected case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_connected_extension_bound__p2m_76736e59_4cf5_41fe_b0de_3723f7df5ba6_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry

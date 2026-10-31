-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_40bf128a_95fa_481c_8fd2_3c8143f624ef_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_40bf128a_95fa_481c_8fd2_3c8143f624ef_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:18:59.309565+00:00
-- url     : https://prove2.me/theorems/dd36cc74-6900-4ba9-ba44-29249813e379
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable simple graph on a finite ordered vertex type is contained in a drawable graph on the same vertices that is maximal among drawable supergraphs; the extension has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_40bf128a_95fa_481c_8fd2_3c8143f624ef_a2 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) : ∃ H : SimpleGraph V, M ≤ H ∧ M.edgeSet.ncard ≤ H.edgeSet.ncard ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ N : SimpleGraph V, H ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ H := by sorry

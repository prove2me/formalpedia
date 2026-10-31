-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_maximal_extension__p2m_71de413d_a2cb_43c4_9595_c6ba34d7c93b_a1
-- name    : WilliamsonShmoys.planar_graph_maximal_extension__p2m_71de413d_a2cb_43c4_9595_c6ba34d7c93b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:05:39.66161+00:00
-- url     : https://prove2.me/theorems/4a31a18e-a2e4-4f80-ae72-d80a221c949e
-- title:
--   Maximal planar extension on a fixed vertex type
-- statement:
--   Every graph on a finite ordered vertex type with at least three vertices and a crossing-free drawing is contained in an inclusion-maximal graph on the same vertex type that also has such a drawing. The extension has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_maximal_extension__p2m_71de413d_a2cb_43c4_9595_c6ba34d7c93b_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 <= Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry

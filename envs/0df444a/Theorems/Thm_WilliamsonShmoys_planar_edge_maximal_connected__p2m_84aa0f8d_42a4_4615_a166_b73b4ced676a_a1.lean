-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_connected__p2m_84aa0f8d_42a4_4615_a166_b73b4ced676a_a1
-- name    : WilliamsonShmoys.planar_edge_maximal_connected__p2m_84aa0f8d_42a4_4615_a166_b73b4ced676a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T01:00:45.874359+00:00
-- url     : https://prove2.me/theorems/8a5c6ab3-e805-464b-b048-a38e7a7d5336
-- title:
--   An edge-maximal planar graph with at least three vertices is connected
-- statement:
--   A planar graph on at least three vertices that has no strictly larger planar supergraph on the same vertices is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_maximal_connected__p2m_84aa0f8d_42a4_4615_a166_b73b4ced676a_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ G : SimpleGraph V, H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G ≤ H) : H.Connected := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_step__p2m_fe481bb3_5bd3_4632_91f8_3ed33818ce05_a1
-- name    : WilliamsonShmoys.planar_drawing_bridge_step__p2m_fe481bb3_5bd3_4632_91f8_3ed33818ce05_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:53:53.534883+00:00
-- url     : https://prove2.me/theorems/4056369d-447b-4f56-af0d-8885c1f945ba
-- title:
--   Add a planar bridge between disconnected parts
-- statement:
--   Any disconnected finite graph with a crossing-free drawing can be extended to a crossing-free drawn supergraph that connects at least one pair of vertices that were previously in different components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_bridge_step__p2m_fe481bb3_5bd3_4632_91f8_3ed33818ce05_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (hGnot : ¬ G.Connected) : ∃ G' : SimpleGraph V, G ≤ G' ∧ HasPlanarDrawingOn G' ∧ ∃ u v : V, ¬ G.Reachable u v ∧ G'.Reachable u v := by sorry

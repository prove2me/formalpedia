-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_bridge__p2m_e3c38815_b74a_4448_8999_9891a739182d_a2
-- name    : WilliamsonShmoys.planar_component_bridge__p2m_e3c38815_b74a_4448_8999_9891a739182d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:03:02.868313+00:00
-- url     : https://prove2.me/theorems/b33f5c89-1d0f-45ec-ac5a-65c11bb5f408
-- title:
--   Planar bridge between disconnected components with at least three vertices
-- statement:
--   A disconnected graph on at least three vertices with a crossing-free drawing has a crossing-free supergraph on the same vertices that preserves existing reachability, does not decrease the edge count, and joins at least one pair that was previously unreachable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_component_bridge__p2m_e3c38815_b74a_4448_8999_9891a739182d_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) (hNotConnected : ¬ G.Connected) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ (∀ u v, G.Reachable u v → H.Reachable u v) ∧ (∃ u v, ¬ G.Reachable u v ∧ H.Reachable u v) := by sorry

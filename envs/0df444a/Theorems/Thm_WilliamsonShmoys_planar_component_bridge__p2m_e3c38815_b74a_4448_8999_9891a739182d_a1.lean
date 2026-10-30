-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_bridge__p2m_e3c38815_b74a_4448_8999_9891a739182d_a1
-- name    : WilliamsonShmoys.planar_component_bridge__p2m_e3c38815_b74a_4448_8999_9891a739182d_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T23:41:51.534466+00:00
-- url     : https://prove2.me/theorems/2f493a8d-2a95-403f-b1d1-fac91c2f8b7f
-- title:
--   Planar bridge between disconnected components
-- statement:
--   A disconnected finite graph with a crossing-free drawing on its ordered vertex type has a crossing-free supergraph on the same vertices that preserves existing reachability and joins at least one pair that was previously in different components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_component_bridge__p2m_e3c38815_b74a_4448_8999_9891a739182d_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hNotConnected : ¬ G.Connected) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ (∀ u v, G.Reachable u v → H.Reachable u v) ∧ (∃ u v, ¬ G.Reachable u v ∧ H.Reachable u v) := by sorry

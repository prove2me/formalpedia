-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_bridge_strict__p2m_b33f5c89_1d0f_45ec_ac5a_65c11bb5f408_a1
-- name    : WilliamsonShmoys.planar_component_bridge_strict__p2m_b33f5c89_1d0f_45ec_ac5a_65c11bb5f408_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:27.797271+00:00
-- url     : https://prove2.me/theorems/654d6b40-351a-4feb-9abd-94332c593474
-- title:
--   Strict planar bridge augmentation for a disconnected drawing
-- statement:
--   A disconnected graph with at least three vertices and a crossing-free drawing admits a crossing-free supergraph on the same vertices that adds at least one edge, preserves all old reachability, and joins a previously unreachable pair.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_component_bridge_strict__p2m_b33f5c89_1d0f_45ec_ac5a_65c11bb5f408_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) (hNotConnected : ¬ G.Connected) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ G.edgeSet.ncard < H.edgeSet.ncard ∧ (∀ u v, G.Reachable u v → H.Reachable u v) ∧ (∃ u v, ¬ G.Reachable u v ∧ H.Reachable u v) := by sorry

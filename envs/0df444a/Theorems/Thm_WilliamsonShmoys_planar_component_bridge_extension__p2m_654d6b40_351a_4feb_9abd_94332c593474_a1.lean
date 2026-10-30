-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_bridge_extension__p2m_654d6b40_351a_4feb_9abd_94332c593474_a1
-- name    : WilliamsonShmoys.planar_component_bridge_extension__p2m_654d6b40_351a_4feb_9abd_94332c593474_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:12:55.181869+00:00
-- url     : https://prove2.me/theorems/afb0646a-1b1c-43fc-91b8-89461203ac52
-- title:
--   Planar drawing extension across disconnected components
-- statement:
--   Given a disconnected graph on at least three vertices with a crossing-free drawing, extend it on the same vertices to a crossing-free supergraph with strictly more edges and an edge joining a pair that was previously unreachable. The independent proof route is to select vertices in distinct components and construct a noncrossing connecting arc after separating the drawn components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_component_bridge_extension__p2m_654d6b40_351a_4feb_9abd_94332c593474_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) (hNotConnected : ¬ G.Connected) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ G.edgeSet.ncard < H.edgeSet.ncard ∧ (∃ u v, ¬ G.Reachable u v ∧ H.Adj u v) := by sorry

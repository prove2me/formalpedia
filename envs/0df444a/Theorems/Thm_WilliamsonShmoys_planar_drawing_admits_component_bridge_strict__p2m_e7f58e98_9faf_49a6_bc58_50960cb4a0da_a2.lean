-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_admits_component_bridge_strict__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a2
-- name    : WilliamsonShmoys.planar_drawing_admits_component_bridge_strict__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:05:45.370171+00:00
-- url     : https://prove2.me/theorems/8e313f52-7cd9-446d-9cbb-05951652d57f
-- title:
--   A planar drawing admits a strict bridge between distinct components
-- statement:
--   Given a planar drawing and two unreachable vertices, extend the graph with an edge between them while preserving a planar drawing; the extension is strict because the new edge connects vertices that were previously in different components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_admits_component_bridge_strict__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V} (hUnreachable : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ K.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K ≠ G := by
  sorry

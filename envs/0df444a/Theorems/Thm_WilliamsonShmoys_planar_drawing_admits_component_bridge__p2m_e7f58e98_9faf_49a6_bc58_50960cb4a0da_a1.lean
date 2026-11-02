-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_admits_component_bridge__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a1
-- name    : WilliamsonShmoys.planar_drawing_admits_component_bridge__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:52:27.721005+00:00
-- url     : https://prove2.me/theorems/fb6ecefe-a7c1-43fd-82b7-639d4eeb4e0f
-- title:
--   A planar drawing can bridge distinct components
-- statement:
--   If two vertices are in distinct components of a graph with a crossing-free drawing, there is a planar drawing of a graph extending the original and containing the edge between those vertices. The core argument routes a simple connector through the unbounded face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_admits_component_bridge__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V} (hUnreachable : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ K.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  sorry

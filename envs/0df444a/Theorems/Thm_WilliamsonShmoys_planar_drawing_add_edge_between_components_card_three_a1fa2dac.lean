-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_components_card_three_a1fa2dac
-- name    : WilliamsonShmoys.planar_drawing_add_edge_between_components_card_three_a1fa2dac
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T14:05:14.760992+00:00
-- url     : https://prove2.me/theorems/8bd5bb2b-358e-4ff5-92a6-74c11d52753d
-- title:
--   Planar drawing extension joining separate components with at least three vertices
-- statement:
--   A disconnected finite graph with at least three vertices and a planar drawing has a strict planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

theorem WilliamsonShmoys.planar_drawing_add_edge_between_components_card_three_a1fa2dac
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ G ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry

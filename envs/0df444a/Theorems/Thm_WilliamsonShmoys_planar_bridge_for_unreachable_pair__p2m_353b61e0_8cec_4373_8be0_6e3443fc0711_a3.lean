-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_bridge_for_unreachable_pair__p2m_353b61e0_8cec_4373_8be0_6e3443fc0711_a3
-- name    : WilliamsonShmoys.planar_bridge_for_unreachable_pair__p2m_353b61e0_8cec_4373_8be0_6e3443fc0711_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:44:00.254579+00:00
-- url     : https://prove2.me/theorems/d8a37a06-a308-40a2-a42a-8503e63d7192
-- title:
--   Planar bridge extension for a specified pair of components
-- statement:
--   For two vertices in different components of a graph with a planar drawing, extend the graph by their edge while preserving a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_bridge_for_unreachable_pair__p2m_353b61e0_8cec_4373_8be0_6e3443fc0711_a3
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (u v : V) (hH : HasPlanarDrawingOn H)
    (huv : ¬ Relation.ReflTransGen H.Adj u v) :
    ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Adj u v := by sorry

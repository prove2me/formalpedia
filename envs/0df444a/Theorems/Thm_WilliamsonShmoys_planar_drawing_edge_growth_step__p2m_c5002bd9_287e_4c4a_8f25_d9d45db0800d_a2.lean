-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_growth_step__p2m_c5002bd9_287e_4c4a_8f25_d9d45db0800d_a2
-- name    : WilliamsonShmoys.planar_drawing_edge_growth_step__p2m_c5002bd9_287e_4c4a_8f25_d9d45db0800d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T01:02:40.955826+00:00
-- url     : https://prove2.me/theorems/a7eeae48-7b6c-4687-bee4-8c8c70dfa864
-- title:
--   Add an edge between components with a planar drawing
-- statement:
--   Every disconnected finite graph with a planar drawing has a planar supergraph on the same vertices with strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_growth_step__p2m_c5002bd9_287e_4c4a_8f25_d9d45db0800d_a2
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) (hdisc : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ HasPlanarDrawingOn H ∧
      Nat.card G.edgeSet < Nat.card H.edgeSet := by sorry

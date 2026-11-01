-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_nonconnected_edge_attachment__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a4
-- name    : WilliamsonShmoys.planar_nonconnected_edge_attachment__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a4
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T22:02:14.403572+00:00
-- url     : https://prove2.me/theorems/1b3c8fd5-103d-4597-a67f-ac93b5d97381
-- title:
--   Attach a planar edge across components
-- statement:
--   For a finite disconnected graph with a planar drawing, choose distinct unreachable vertices and extend the graph by exactly their edge while retaining a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_nonconnected_edge_attachment__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hdis : ¬ G.Connected) :
    ∃ (u v : V) (huv : u ≠ v),
      ¬ G.Reachable u v ∧
      ∃ H : SimpleGraph V,
        G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ a b, H.Adj a b ↔
          G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by sorry

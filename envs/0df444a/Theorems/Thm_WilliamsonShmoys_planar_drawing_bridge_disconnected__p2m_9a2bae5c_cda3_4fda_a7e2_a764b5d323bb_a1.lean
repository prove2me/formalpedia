-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_disconnected__p2m_9a2bae5c_cda3_4fda_a7e2_a764b5d323bb_a1
-- name    : WilliamsonShmoys.planar_drawing_bridge_disconnected__p2m_9a2bae5c_cda3_4fda_a7e2_a764b5d323bb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:02:16.677267+00:00
-- url     : https://prove2.me/theorems/3eced331-e15d-452f-ac43-a684696313f5
-- title:
--   Bridge disconnected vertices in a planar drawing
-- statement:
--   Adding one edge between vertices in different connected components of a planar graph preserves the existence of a planar drawing, with the resulting adjacency relation exactly the original edges plus that edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_bridge_disconnected__p2m_9a2bae5c_cda3_4fda_a7e2_a764b5d323bb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V)
    (hdisconnected : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      (∀ a b, H.Adj a b ↔
        G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry

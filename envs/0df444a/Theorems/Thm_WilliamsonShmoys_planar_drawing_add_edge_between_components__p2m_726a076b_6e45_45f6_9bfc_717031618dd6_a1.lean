-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_components__p2m_726a076b_6e45_45f6_9bfc_717031618dd6_a1
-- name    : WilliamsonShmoys.planar_drawing_add_edge_between_components__p2m_726a076b_6e45_45f6_9bfc_717031618dd6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:12:22.608319+00:00
-- url     : https://prove2.me/theorems/8933b290-830c-4273-b772-22a4e7f72afb
-- title:
--   Add an edge between disconnected planar components
-- statement:
--   If `u` and `v` are in different connected components of a graph with a crossing-free drawing, adding exactly the edge between them preserves the existence of such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_between_components__p2m_726a076b_6e45_45f6_9bfc_717031618dd6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (hdisj : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      (∀ a b, H.Adj a b ↔
        G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry

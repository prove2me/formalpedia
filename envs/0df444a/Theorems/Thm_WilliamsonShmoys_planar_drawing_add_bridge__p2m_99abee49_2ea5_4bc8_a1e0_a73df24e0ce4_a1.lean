-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge__p2m_99abee49_2ea5_4bc8_a1e0_a73df24e0ce4_a1
-- name    : WilliamsonShmoys.planar_drawing_add_bridge__p2m_99abee49_2ea5_4bc8_a1e0_a73df24e0ce4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:56:25.945371+00:00
-- url     : https://prove2.me/theorems/c25e31c2-3944-4e71-be02-9fbfc136a4b1
-- title:
--   Add a planar bridge between disconnected vertices
-- statement:
--   For a finite graph with a planar drawing, adding one edge between vertices in different connected components yields a graph that still has a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_bridge__p2m_99abee49_2ea5_4bc8_a1e0_a73df24e0ce4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (hnot : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      (∀ a b, H.Adj a b ↔
        G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry

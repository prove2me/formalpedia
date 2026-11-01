-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_single_edge_extension__p2m_c8d20c40_a498_43d8_b4ed_abd0723d73a4_a1
-- name    : WilliamsonShmoys.planar_drawingOn_single_edge_extension__p2m_c8d20c40_a498_43d8_b4ed_abd0723d73a4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:32:37.341523+00:00
-- url     : https://prove2.me/theorems/bde12a09-c3ff-49b5-827a-2421e10fc278
-- title:
--   Planar drawing after adding exactly one edge between components
-- statement:
--   A planar drawing can be redrawn so that the resulting graph contains precisely the original edges together with the edge between the two specified unreachable vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_single_edge_extension__p2m_c8d20c40_a498_43d8_b4ed_abd0723d73a4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (u v : V)
    (hdisj : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ a b, H.Adj a b ↔
        G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u)) := by sorry

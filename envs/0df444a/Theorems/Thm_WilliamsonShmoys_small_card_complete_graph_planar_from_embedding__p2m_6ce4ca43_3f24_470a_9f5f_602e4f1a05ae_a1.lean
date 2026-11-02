-- Prove2me | Theorems.Thm_WilliamsonShmoys_small_card_complete_graph_planar_from_embedding__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1
-- name    : WilliamsonShmoys.small_card_complete_graph_planar_from_embedding__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:53:13.203535+00:00
-- url     : https://prove2.me/theorems/8ad4d3a8-78f8-40f6-aebf-b2ce53dffd6a
-- title:
--   Planar drawing of a complete graph on fewer than three vertices
-- statement:
--   An injective placement of fewer than three vertices in the plane induces a crossing-free drawing of the complete graph on those vertices, using straight-line arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.small_card_complete_graph_planar_from_embedding__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (p : V → ℝ × ℝ) (hp : Function.Injective p)
    (hsmall : Fintype.card V < 3) :
    HasPlanarDrawingOn (⊤ : SimpleGraph V) := by
  sorry

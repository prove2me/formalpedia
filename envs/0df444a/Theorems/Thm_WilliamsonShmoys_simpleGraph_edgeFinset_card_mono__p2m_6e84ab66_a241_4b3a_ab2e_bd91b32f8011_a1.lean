-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeFinset_card_mono__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
-- name    : WilliamsonShmoys.simpleGraph_edgeFinset_card_mono__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:13:29.587708+00:00
-- url     : https://prove2.me/theorems/6e83f2d4-09da-413b-bbbb-362428f64611
-- title:
--   Monotonicity of finite edge counts
-- statement:
--   If one simple graph is a subgraph of another on the same finite vertex type, its finite edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_edgeFinset_card_mono__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1 {V : Type} [Fintype V] {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G ≤ H) : G.edgeFinset.card ≤ H.edgeFinset.card := by sorry

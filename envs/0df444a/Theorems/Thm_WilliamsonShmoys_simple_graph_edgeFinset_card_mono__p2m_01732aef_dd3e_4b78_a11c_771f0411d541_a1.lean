-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_graph_edgeFinset_card_mono__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1
-- name    : WilliamsonShmoys.simple_graph_edgeFinset_card_mono__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:58:47.832614+00:00
-- url     : https://prove2.me/theorems/950dbba2-798f-4873-9a3a-67b752e4e85f
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   If one simple graph is a subgraph of another on the same finite vertex type, its edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.simple_graph_edgeFinset_card_mono__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) (hKH : K ≤ H) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj; K.edgeFinset.card) ≤
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj; H.edgeFinset.card) := by sorry

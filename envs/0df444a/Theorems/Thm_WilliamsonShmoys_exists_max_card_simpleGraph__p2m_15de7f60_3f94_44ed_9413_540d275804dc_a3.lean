-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_card_simpleGraph__p2m_15de7f60_3f94_44ed_9413_540d275804dc_a3
-- name    : WilliamsonShmoys.exists_max_card_simpleGraph__p2m_15de7f60_3f94_44ed_9413_540d275804dc_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:12:16.389108+00:00
-- url     : https://prove2.me/theorems/ccf27c3c-c0ad-4ac3-a372-76803cb5cda5
-- title:
--   Maximum edge count in a nonempty family of simple graphs
-- statement:
--   Every nonempty family of simple graphs on a finite vertex type with decidable equality contains a graph whose edge count is at least that of every other member.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_max_card_simpleGraph__p2m_15de7f60_3f94_44ed_9413_540d275804dc_a3
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop) (G₀ : SimpleGraph V) (h₀ : P G₀) :
    ∃ G : SimpleGraph V, P G ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       ∀ H : SimpleGraph V, P H →
         letI : DecidableRel H.Adj := Classical.decRel H.Adj
         H.edgeFinset.card ≤ G.edgeFinset.card) := by sorry

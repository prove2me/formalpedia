-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_adjacency_card_strict__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2
-- name    : WilliamsonShmoys.simpleGraph_adjacency_card_strict__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:18:54.235207+00:00
-- url     : https://prove2.me/theorems/9e772b9a-d288-483c-a537-2cf4f59d7709
-- title:
--   Strict adjacency-count increase under proper extension
-- statement:
--   For finite simple graphs with decidable adjacency, proper graph inclusion strictly increases the number of ordered adjacent vertex pairs. Inclusion gives a subset relation, and graph inequality provides an adjacent pair in the difference, so finite cardinality increases strictly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_adjacency_card_strict__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a2
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) (hne : G ≠ H) :
    Fintype.card {p : V × V // G.Adj p.1 p.2} <
      Fintype.card {p : V × V // H.Adj p.1 p.2} := by sorry

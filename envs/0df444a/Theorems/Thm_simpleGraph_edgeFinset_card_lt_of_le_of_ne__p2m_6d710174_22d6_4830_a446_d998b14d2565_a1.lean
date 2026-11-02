-- Prove2me | Theorems.Thm_simpleGraph_edgeFinset_card_lt_of_le_of_ne__p2m_6d710174_22d6_4830_a446_d998b14d2565_a1
-- name    : simpleGraph_edgeFinset_card_lt_of_le_of_ne__p2m_6d710174_22d6_4830_a446_d998b14d2565_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:40:57.245238+00:00
-- url     : https://prove2.me/theorems/2fb786b2-edb0-40a3-a9ee-3d0b894437f6
-- title:
--   Proper finite graph inclusion increases edge count
-- statement:
--   For finite simple graphs on the same vertex type, strict subgraph inclusion strictly increases the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem simpleGraph_edgeFinset_card_lt_of_le_of_ne__p2m_6d710174_22d6_4830_a446_d998b14d2565_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) (hne : G ≠ H) :
    G.edgeFinset.card < H.edgeFinset.card := by sorry

-- Prove2me | Theorems.Thm_crossing_adjacency_makes_strict_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
-- name    : crossing_adjacency_makes_strict_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:52:59.19862+00:00
-- url     : https://prove2.me/theorems/3e8a20ae-0ab9-4ff0-aa18-ab4804a350f8
-- title:
--   A newly added adjacency makes graph inclusion strict
-- statement:
--   If H contains all edges of G and has an adjacency absent from G, then G is strictly below H in the graph order.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem crossing_adjacency_makes_strict_extension__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (hGH : G ≤ H)
    (u v : V) (hG : ¬ G.Adj u v) (hH : H.Adj u v) : G < H := by sorry

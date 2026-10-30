-- Prove2me | Theorems.Thm_WilliamsonShmoys_ordered_adj_card_eq_rigidity__p2m_056354fe_8081_4e5e_ae62_0d709f8aad22_a1
-- name    : WilliamsonShmoys.ordered_adj_card_eq_rigidity__p2m_056354fe_8081_4e5e_ae62_0d709f8aad22_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:04:54.018564+00:00
-- url     : https://prove2.me/theorems/b19ad759-cedf-46ba-a728-553a135768e9
-- title:
--   Equal ordered-adjacency cardinality forces graph equality
-- statement:
--   For simple graphs on a finite vertex type, if one graph contains another and their ordered adjacency-pair cardinalities are equal, then the graphs are equal by inclusion in both directions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.ordered_adj_card_eq_rigidity__p2m_056354fe_8081_4e5e_ae62_0d709f8aad22_a1 {V : Type} [Fintype V] (K L : SimpleGraph V) (hKL : K ≤ L) (hcard : Nat.card {p : V × V // L.Adj p.1 p.2} = Nat.card {p : V × V // K.Adj p.1 p.2}) : L ≤ K := by sorry

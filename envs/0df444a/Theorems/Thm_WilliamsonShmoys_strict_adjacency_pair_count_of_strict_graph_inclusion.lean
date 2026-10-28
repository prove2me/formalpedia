-- Prove2me | Theorems.Thm_WilliamsonShmoys_strict_adjacency_pair_count_of_strict_graph_inclusion
-- name    : WilliamsonShmoys.strict_adjacency_pair_count_of_strict_graph_inclusion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:00:06.407929+00:00
-- url     : https://prove2.me/theorems/9479dde3-4eba-4bec-8cfc-1ba849842979
-- title:
--   Proper graph inclusion increases the adjacent-pair count
-- statement:
--   For finite V, proper inclusion of simple graphs strictly increases the number of ordered adjacent vertex pairs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.strict_adjacency_pair_count_of_strict_graph_inclusion
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V) (hKL : LE.le K L) (hneq : L ≠ K) :
    Nat.card {p : V × V // K.Adj p.1 p.2} <
      Nat.card {p : V × V // L.Adj p.1 p.2} := by sorry

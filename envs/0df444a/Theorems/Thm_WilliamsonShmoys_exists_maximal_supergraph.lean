-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph
-- name    : WilliamsonShmoys.exists_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:42:11.251945+00:00
-- url     : https://prove2.me/theorems/24e4ded1-e781-4419-b985-5ad79f5a3c6c
-- title:
--   Maximal element among finite graph extensions
-- statement:
--   For a finite vertex type, any property satisfied by a graph L has a supergraph satisfying that property which is maximal under inclusion among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph
    {V : Type} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hL : P L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ P M ∧
      ∀ N : SimpleGraph V, M ≤ N → P N → N = M := by sorry

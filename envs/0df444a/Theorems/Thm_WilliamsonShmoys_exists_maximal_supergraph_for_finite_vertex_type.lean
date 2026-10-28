-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_vertex_type
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_finite_vertex_type
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:28:11.29182+00:00
-- url     : https://prove2.me/theorems/7f10e8fb-43e1-4e84-af33-82606faa7bbc
-- title:
--   Maximal supergraphs for predicates on finite graphs
-- statement:
--   For any predicate on simple graphs over a finite vertex type, every graph satisfying the predicate has a supergraph satisfying it that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_for_finite_vertex_type
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (L : SimpleGraph V)
    (hL : P L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ P M ∧
      ∀ N : SimpleGraph V, M ≤ N → P N → N ≤ M := by sorry

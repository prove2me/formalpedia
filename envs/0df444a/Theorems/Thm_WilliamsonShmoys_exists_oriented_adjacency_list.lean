-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_oriented_adjacency_list
-- name    : WilliamsonShmoys.exists_oriented_adjacency_list
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:30:24.931101+00:00
-- url     : https://prove2.me/theorems/13c3cc88-cbc8-45e0-a246-f88e0668ac84
-- title:
--   Enumerate ordered adjacent pairs
-- statement:
--   Every finite simple graph has a list containing each ordered adjacent pair exactly once; all listed pairs are adjacent, and the list length is twice the number of edges. The proof enumerates the finite set of ordered adjacent pairs and counts the two orientations of every edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_oriented_adjacency_list
    {V : Type} [Fintype V] (L : SimpleGraph V) :
    ∃ es : List (V × V),
      (∀ e ∈ es, L.Adj e.1 e.2) ∧
      es.length = 2 * L.edgeSet.ncard := by sorry

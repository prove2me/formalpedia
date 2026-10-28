-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_count_maximal_supergraph
-- name    : WilliamsonShmoys.exists_edge_count_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:20:59.421984+00:00
-- url     : https://prove2.me/theorems/e5b96e32-f1e3-43b7-ad6a-050b5a4d86f1
-- title:
--   A finite graph predicate has an edge-maximal supergraph
-- statement:
--   For any predicate on simple graphs over a finite ordered vertex type, if the predicate holds for a graph K, then some predicate-satisfying supergraph L of K has at least as many edges as every predicate-satisfying supergraph of L.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_edge_count_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      P L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        P M →
        M.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_predicate
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_predicate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:18:51.277744+00:00
-- url     : https://prove2.me/theorems/bd15d0b7-cf3b-4839-ae54-37a42273f195
-- title:
--   Maximal feasible supergraph on a finite vertex type
-- statement:
--   For any property of simple graphs on a fixed finite linearly ordered vertex type, if the property holds for a graph M, there is a supergraph N satisfying the property such that every property-satisfying supergraph of N is already a subgraph of N.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_for_predicate
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (M : SimpleGraph V) (hP : P M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ P N ∧
      ∀ K : SimpleGraph V, N ≤ K → P K → K ≤ N := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_on_finite_vertex_type
-- name    : WilliamsonShmoys.exists_maximal_supergraph_on_finite_vertex_type
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:44:54.07162+00:00
-- url     : https://prove2.me/theorems/64b5e1e3-8459-4d14-b1b8-cd5316b58593
-- title:
--   Maximal predicate supergraph on a finite vertex type
-- statement:
--   For any property of simple graphs on a fixed finite linearly ordered vertex type, every graph satisfying the property has a supergraph satisfying it that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_on_finite_vertex_type
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (N : SimpleGraph V)
    (hP : P N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ P K ∧
      (∀ L : SimpleGraph V, K ≤ L → P L → L = K) := by sorry

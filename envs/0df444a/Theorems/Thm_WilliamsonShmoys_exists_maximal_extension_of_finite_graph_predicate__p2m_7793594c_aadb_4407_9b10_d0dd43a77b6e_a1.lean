-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_finite_graph_predicate__p2m_7793594c_aadb_4407_9b10_d0dd43a77b6e_a1
-- name    : WilliamsonShmoys.exists_maximal_extension_of_finite_graph_predicate__p2m_7793594c_aadb_4407_9b10_d0dd43a77b6e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:49.90584+00:00
-- url     : https://prove2.me/theorems/3d5692d7-4e31-4e00-99ee-e6ddc67b947a
-- title:
--   Maximal extension for a hereditary graph predicate on a finite vertex type
-- statement:
--   For any hereditary predicate P on simple graphs over a finite vertex type, every graph satisfying P has a P-satisfying supergraph that is maximal under subgraph inclusion and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_extension_of_finite_graph_predicate__p2m_7793594c_aadb_4407_9b10_d0dd43a77b6e_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop) (H : SimpleGraph V)
    (hP : P H)
    (hereditary : ∀ ⦃G K : SimpleGraph V⦄, G ≤ K → P K → P G) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      P K ∧
      (∀ L : SimpleGraph V, K ≤ L → P L → L = K) := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_component_partition_core__p2m_43810500_1f43_4f26_9fb2_357a895d104d_a1
-- name    : WilliamsonShmoys.finite_component_partition_core__p2m_43810500_1f43_4f26_9fb2_357a895d104d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:33:42.14684+00:00
-- url     : https://prove2.me/theorems/8f30f87d-38e5-4ef0-b028-5aec7827f5e7
-- title:
--   Finite connected-component partition core
-- statement:
--   Every finite simple graph has a partition into nonempty, pairwise disjoint blocks covering all vertices, with exact vertex-cardinality sum. Each block induces a connected graph, and blocks of size one or two satisfy the specified edge bounds. The empty graph is covered by the empty partition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_component_partition_core__p2m_43810500_1f43_4f26_9fb2_357a895d104d_a1
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     ∃ C : Finset (Finset V),
      (∀ B ∈ C, 0 < B.card) ∧
      (∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ →
        Disjoint (↑B₁ : Set V) (↑B₂ : Set V)) ∧
      (∀ v : V, ∃ B ∈ C, v ∈ B) ∧
      Fintype.card V = ∑ B ∈ C, B.card ∧
      (∀ B ∈ C,
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).Connected) ∧
      (∀ B ∈ C, B.card = 1 →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).edgeFinset.card = 0) ∧
      (∀ B ∈ C, B.card = 2 →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).edgeFinset.card ≤ 1)) := by sorry

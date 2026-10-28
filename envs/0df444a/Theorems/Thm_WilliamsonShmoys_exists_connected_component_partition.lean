-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_component_partition
-- name    : WilliamsonShmoys.exists_connected_component_partition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:02:09.391266+00:00
-- url     : https://prove2.me/theorems/865ff75b-256e-4bfe-b4e5-415cc2f2683c
-- title:
--   Connected components form an edge-respecting finite partition
-- statement:
--   Every finite simple graph's vertices can be partitioned into the vertex sets of its connected components. Each block induces a connected graph, distinct blocks are disjoint, and adjacent vertices lie in the same block. A proof route is to use the equivalence relation of mutual reachability, enumerate its finitely many equivalence classes, and establish these properties from reachability.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_connected_component_partition
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) :
    ∃ C : Finset (Finset V),
      (∀ v : V, ∃ S, S ∈ C ∧ v ∈ S) ∧
      (∀ S, S ∈ C → ∀ T, T ∈ C → S ≠ T → Disjoint S T) ∧
      (∀ S, S ∈ C → (G.induce (↑S : Set V)).Connected) ∧
      (∀ ⦃u v : V⦄, G.Adj u v → ∃ S, S ∈ C ∧ u ∈ S ∧ v ∈ S) := by sorry
